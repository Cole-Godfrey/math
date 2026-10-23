"""exercise proof extraction, audit failures, provenance, and exploration."""

from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
import gc
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from repository.__main__ import main
from repository.build import find_lake, input_hashes, load_catalog, proof_export_path, run, verify
from repository.core import ExpressionPool, RepositoryError, axiom_closure, canonical_chunks, dependency_path, validate
from repository.explore import KnowledgeGraph
from repository.store import open_snapshot


ROOT = Path(__file__).resolve().parents[1]


class RepositoryArtifacts:
    """copy locked sources and proof artifacts for isolated checks."""

    def clone_inputs(self, root: Path) -> None:
        for relative in input_hashes(ROOT):
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)
        (root / ".lake").mkdir(exist_ok=True)
        (root / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)

    def clone_artifact(self, root: Path) -> None:
        (root / "build").mkdir()
        source = proof_export_path(ROOT, self.catalog)
        shutil.copyfile(source, root / "build" / source.name)
        shutil.copyfile(ROOT / "build/knowledge.json", root / "build/knowledge.json")


class RepositoryTests(RepositoryArtifacts, unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.catalog = verify(ROOT, clean=True)
        cls.nodes = {node["name"]: node for node in cls.catalog["declarations"]}
        cls.policy = json.loads((ROOT / "knowledge.json").read_text())
        cls.lake = find_lake(ROOT)

    @classmethod
    def tearDownClass(cls):
        cls.nodes.clear()
        cls.catalog.clear()
        gc.collect()

    def mutated(self, name: str) -> tuple[dict, dict]:
        raw = {**self.catalog, "declarations": self.catalog["declarations"].copy()}
        index = next(i for i, node in enumerate(raw["declarations"]) if node["name"] == name)
        node = deepcopy(raw["declarations"][index])
        raw["declarations"][index] = node
        return raw, node

    def test_foundation_axioms_are_exact(self):
        self.assertIn("nanoda_bin 0.4.19", self.catalog["provenance"]["checkers"])
        self.assertEqual(set(self.nodes["Math.Logic.Classical.excluded_middle"]["axioms"]),
                         {"propext", "Quot.sound", "Classical.choice"})
        self.assertEqual(set(self.nodes["Math.Sets.ext"]["axioms"]), {"propext", "Quot.sound"})
        for name in self.catalog["roots"]:
            if self.nodes[name]["module"] in {"Math.Logic.Basic", "Math.Numbers.Natural"}:
                self.assertEqual(self.nodes[name]["axioms"], [], name)

    def test_source_and_proof_are_available(self):
        node = self.nodes["Math.Natural.mul_assoc"]
        self.assertGreater(node["source"]["line"], 0)
        self.assertIsInstance(node["value"], int)
        self.assertEqual(self.catalog["expressions"][node["value"]]["tag"], "lam")
        self.assertIn("Nat.rec", node["proof"])
        self.assertIn("Math.Natural.mul_add", node["dependencies"])

    def test_modules_follow_import_order(self):
        order = self.catalog["module_order"]
        for module in self.catalog["modules"]:
            if module["name"] in order:
                for dependency in module["imports"]:
                    if dependency in order:
                        self.assertLess(order.index(dependency), order.index(module["name"]))

    def test_axiom_paths_have_real_edges(self):
        start = "Math.Logic.Classical.excluded_middle"
        for target in self.nodes[start]["axioms"]:
            path = dependency_path(self.nodes, start, target)
            self.assertEqual(path[0], start)
            self.assertEqual(path[-1], target)
            for source, destination in zip(path, path[1:]):
                self.assertIn(destination, self.nodes[source]["dependencies"])
        self.assertIsNone(dependency_path(self.nodes, "Math.Logic.identity", "Classical.choice"))

    def test_inductive_cycles_preserve_axiom_closure(self):
        nodes = {
            "A": {"kind": "inductive", "dependencies": ["B"]},
            "B": {"kind": "constructor", "dependencies": ["A", "hypothesis"]},
            "hypothesis": {"kind": "axiom", "dependencies": []},
        }
        self.assertEqual(axiom_closure(nodes), {name: {"hypothesis"} for name in nodes})

    def test_missing_declaration_is_rejected(self):
        raw = self.catalog.copy()
        raw["declarations"] = [n for n in raw["declarations"] if n["name"] != "Eq"]
        with self.assertRaisesRegex(RepositoryError, "unresolved dependency"):
            validate(raw, self.policy)

    def test_fabricated_edges_are_rejected(self):
        raw, node = self.mutated("Math.Natural.mul_assoc")
        node["dependencies"].remove("Math.Natural.mul_add")
        with self.assertRaisesRegex(RepositoryError, "dependencies differ from declared expression roles"):
            validate(raw, self.policy)

    def test_fabricated_axiom_summary_is_rejected(self):
        raw, node = self.mutated("Math.Sets.ext")
        node["axioms"] = []
        with self.assertRaisesRegex(RepositoryError, "axiom closure differs from fresh Lean traversal"):
            validate(raw, self.policy)

    def test_missing_proof_is_rejected(self):
        raw, node = self.mutated("Math.Natural.mul_assoc")
        node["value"] = None
        with self.assertRaisesRegex(RepositoryError, "missing or unexpected body"):
            validate(raw, self.policy)

    def test_recursor_rules_are_audited(self):
        for reference in (None, True, -1, len(self.catalog["expressions"]), {"tag": "mvar", "name": "unresolved"}):
            with self.subTest(reference=reference):
                raw, node = self.mutated("Nat.rec")
                node["structure"]["rules"][0]["rhs"] = reference
                with patch("repository.core.ExpressionPool", side_effect=AssertionError("term audit allocated")):
                    with self.assertRaisesRegex(RepositoryError, "invalid expression reference"):
                        validate(raw, self.policy)

    def test_free_variables_are_rejected(self):
        for expression in ({"tag": "fvar", "name": "x"}, {"tag": "bvar", "index": 0}):
            raw, node = self.mutated("Math.Logic.truth")
            node["value"] = expression
            with self.assertRaises(RepositoryError):
                validate(raw, self.policy)

    def test_unsafe_declarations_are_rejected(self):
        raw, node = self.mutated("Math.Logic.truth")
        node["unsafe"] = True
        with self.assertRaisesRegex(RepositoryError, "unsafe declaration"):
            validate(raw, self.policy)

    def test_project_declarations_cannot_be_omitted(self):
        raw = {**self.catalog, "roots": self.catalog["roots"].copy()}
        raw["roots"].remove("Math.Logic.identity")
        with self.assertRaisesRegex(RepositoryError, "declaration inventory is incomplete"):
            validate(raw, self.policy)

    def test_duplicate_names_are_rejected(self):
        raw = {**self.catalog, "declarations": self.catalog["declarations"].copy()}
        raw["declarations"].append(raw["declarations"][0])
        with self.assertRaisesRegex(RepositoryError, "duplicate declaration"):
            validate(raw, self.policy)

    def test_incomplete_proofs_cannot_be_allowlisted(self):
        policy = deepcopy(self.policy)
        policy["axioms"]["sorryAx"] = {"description": "admission", "reference": "test"}
        with self.assertRaisesRegex(RepositoryError, "forbidden axiom"):
            validate(self.catalog, policy)

    def test_cli_shows_proofs_and_axioms(self):
        output = io.StringIO()
        with redirect_stdout(output):
            code = main(["show", "Math.Natural.mul_assoc", "--proof"])
        self.assertEqual(code, 0)
        self.assertIn("Term:", output.getvalue())
        self.assertIn("Axioms: none beyond kernel rules", output.getvalue())

    def test_cli_unknown_name_fails(self):
        output = io.StringIO()
        with redirect_stderr(output):
            code = main(["show", "Math.nonexistent"])
        self.assertEqual(code, 1)
        self.assertIn("unknown declaration", output.getvalue())

    def assert_bad_contribution(self, source: str, expected: str, allowed: list | None = None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.clone_inputs(root)
            (root / "metamath-lock.json").unlink(missing_ok=True)
            aggregate = root / "Math.lean"
            aggregate.write_text("import Math.Adversarial\n")
            shutil.rmtree(root / "Math")
            (root / "Math").mkdir()
            (root / "Math/Adversarial.lean").write_text(source)
            policy = deepcopy(self.policy)
            policy.pop("libraries", None)
            policy.pop("subjects", None)
            policy["modules"] = {
                "Math": {"title": "Mathematics", "allowed_axioms": []},
                "Math.Adversarial": {"title": "Adversarial fixture", "allowed_axioms": allowed or []},
            }
            (root / "lakefile.toml").write_text(
                'name = "math"\ndefaultTargets = ["Math"]\n'
                '[leanOptions]\nautoImplicit = false\nwarningAsError = true\n'
                '[[lean_lib]]\nname = "Math"\n')
            lock = json.loads((root / "lake-manifest.json").read_text())
            lock["packages"] = []
            (root / "lake-manifest.json").write_text(json.dumps(lock))
            (root / "knowledge.json").write_text(json.dumps(policy))
            with patch.dict(os.environ, {"MATH_LAKE": self.lake}):
                with self.assertRaisesRegex(RepositoryError, expected):
                    verify(root)
            self.assertFalse((root / "build/knowledge.json").exists())

    def test_lean_rejects_false_proof(self):
        self.assert_bad_contribution("theorem invalid : False := True.intro\n", "command failed")

    def test_admission_is_detected_after_compilation(self):
        # disable the warning to exercise the dependency audit itself.
        self.assert_bad_contribution(
            "set_option warningAsError false\n"
            "theorem admitted : False := by sorry\n", "unpermitted axiom")

    def test_axiom_outside_project_namespace_is_detected(self):
        self.assert_bad_contribution(
            "axiom hidden : False\ntheorem derived : False := hidden\n",
            "unpermitted axiom")

    def test_classical_axiom_budget_is_enforced(self):
        self.assert_bad_contribution(
            "theorem classical_result (P : Prop) : P ∨ ¬ P := Classical.em P\n",
            "module axiom budget exceeded")

    def test_compiler_based_proof_is_rejected(self):
        self.assert_bad_contribution(
            "import Lean\ntheorem native_result : (List.range 10).length = 10 := by native_decide\n",
            "unpermitted axiom")

    def test_unchecked_kernel_insertion_is_rejected(self):
        self.assert_bad_contribution(
            "import Lean\n"
            "set_option debug.skipKernelTC true in\n"
            "run_elab do\n"
            "  Lean.addDecl (.thmDecl {\n"
            "    name := `unchecked\n"
            "    levelParams := []\n"
            "    type := Lean.mkConst ``False\n"
            "    value := Lean.mkConst ``True.intro\n"
            "  })\n", "leanchecker")

    def test_sources_outside_mathematical_tree_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.clone_inputs(root)
            (root / "Other.lean").write_text("theorem omitted : True := True.intro\n")
            with self.assertRaisesRegex(RepositoryError, "sources must be inside Math"):
                verify(root)

    def test_lake_override_preserves_elan_shim_name(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "elan"
            target.touch()
            shim = Path(directory) / "lake"
            shim.symlink_to(target)
            with patch.dict(os.environ, {"MATH_LAKE": str(shim)}):
                self.assertEqual(find_lake(ROOT), str(shim))

    def test_upstream_declarations_keep_names_and_sources(self):
        name = "Nat.exists_infinite_primes"
        self.assertIn(name, self.catalog["roots"])
        node = self.nodes[name]
        self.assertEqual(node["module"], "Mathlib.Data.Nat.Prime.Infinite")
        self.assertIn("infinitude of primes", node["doc"])
        origin = self.catalog["sources"][node["module"]]
        self.assertEqual(origin["package"], "mathlib")
        self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
        self.assertIn(origin["revision"], origin["url"])
        self.assertIn("Authors:", origin["notice"])
        self.assertEqual(origin["license"], "Apache-2.0")
        self.assertIn("Apache License", self.catalog["provenance"]["dependencies"]["mathlib"]["licenses"]["LICENSE"]["text"])
        for axiom in node["axioms"]:
            self.assertIsNotNone(dependency_path(self.nodes, name, axiom))

    def test_shared_binders_are_checked_in_each_context(self):
        pool = ExpressionPool([
            {"tag": "sort", "level": {"tag": "zero"}}, {"tag": "bvar", "index": 0},
            {"tag": "lam", "name": "x", "type": 0, "body": 1, "binder": "explicit"},
        ])
        self.assertEqual(pool.references(2, set()), set())
        with self.assertRaisesRegex(RepositoryError, "unbound variable"):
            pool.references(1, set())

    def test_expression_cycles_and_forward_references_are_rejected(self):
        with self.assertRaisesRegex(RepositoryError, "earlier nodes"):
            ExpressionPool([{"tag": "app", "function": 0, "argument": 0}])

    def test_expression_hashes_ignore_pool_numbering(self):
        term = {"tag": "const", "name": "True", "levels": []}
        first = ExpressionPool([term])
        second = ExpressionPool([{"tag": "nat", "value": 0}, term])
        self.assertEqual(first.hashes[0], second.hashes[1])

    def test_runtime_helpers_are_separate_from_mathematical_proofs(self):
        name = "Nat.minFacAux._unsafe_rec"
        entries = {entry["name"]: entry for entry in self.catalog["nonlogical_declarations"]}
        self.assertEqual(entries[name]["safety"], "partial")
        self.assertIn(name, self.catalog["module_declarations"])
        self.assertNotIn(name, self.catalog["roots"])
        self.assertNotIn(name, self.nodes)
        self.assertFalse(any(name in node["dependencies"] for node in self.nodes.values()))

    def test_partial_functions_in_project_modules_are_rejected(self):
        self.assert_bad_contribution("partial def loop (n : Nat) : Nat := loop n\n",
                                     "partial declarations are not allowed in project modules")

    def test_partial_proof_dependency_is_rejected(self):
        raw, node = self.mutated("Math.Logic.truth")
        node["partial"] = True
        with self.assertRaisesRegex(RepositoryError, "partial declaration in proof dependency closure"):
            validate(raw, self.policy)

    def test_broad_mathematical_objects_and_theorems_are_indexed(self):
        expected = {
            "Real": "Mathlib.Basic.Real.Basic",
            "TopologicalSpace": "Mathlib.Topology.Defs.Basic",
            "Module.Basis": "Mathlib.LinearAlgebra.Basis.Defs",
            "PMF": "Mathlib.Probability.ProbabilityMassFunction.Basic",
            "exists_hasDerivAt_eq_slope": "Mathlib.Analysis.Calculus.Deriv.MeanValue",
        }
        for name, module in expected.items():
            self.assertIn(name, self.catalog["roots"])
            self.assertEqual(self.nodes[name]["module"], module)
            self.assertTrue(set(self.nodes[name]["axioms"]) <= self.policy["axioms"].keys())

    def test_real_number_printing_code_cannot_enter_proofs(self):
        entries = {entry["name"]: entry for entry in self.catalog["nonlogical_declarations"]}
        self.assertEqual(entries["Real.instRepr"]["safety"], "unsafe")
        self.assertNotIn("Real.instRepr", self.nodes)
        self.assertNotIn("lcProof", self.nodes)
        self.assertNotIn("Quot.unquot", self.nodes)

    def test_mean_value_hierarchy_reaches_its_foundational_objects(self):
        graph = KnowledgeGraph(self.catalog).hierarchy("exists_hasDerivAt_eq_slope")
        names = {node["name"] for node in graph["declarations"]}
        self.assertTrue({"Real", "TopologicalSpace", "HasDerivAt", "ContinuousOn"} <= names)
        self.assertEqual(set(graph["axiom_paths"]), set(self.nodes["exists_hasDerivAt_eq_slope"]["axioms"]))

    def test_expanded_mathematical_objects_are_selected_with_their_original_names(self):
        expected = {
            "Complex": "Mathlib.Basic.Complex.Basic",
            "Preorder": "Mathlib.Order.Defs.PartialOrder",
            "PartialOrder": "Mathlib.Order.Defs.PartialOrder",
            "HasRankNullity": "Mathlib.LinearAlgebra.Dimension.RankNullity",
            "Sylow": "Mathlib.GroupTheory.Sylow",
            "SimpleGraph": "Mathlib.Combinatorics.SimpleGraph.Basic",
            "MeasurableSpace": "Mathlib.MeasureTheory.MeasurableSpace.Defs",
            "MeasureTheory.Measure": "Mathlib.MeasureTheory.Measure.MeasureSpaceDef",
            "MeasureTheory.integral": "Mathlib.MeasureTheory.Integral.Bochner.Basic",
            "CategoryTheory.Category": "Mathlib.CategoryTheory.Category.Basic",
            "CategoryTheory.Functor": "Mathlib.CategoryTheory.Functor.Basic",
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                self.assertEqual(self.nodes[name]["module"], module)

    def test_landmark_results_retain_complete_bodies_and_pinned_attribution(self):
        expected = {
            "zorn_le₀": "Mathlib.Order.Zorn",
            "Function.Embedding.schroeder_bernstein": "Mathlib.SetTheory.Cardinal.SchroederBernstein",
            "Complex.exists_root": "Mathlib.Analysis.Complex.Polynomial.Basic",
            "Complex.isAlgClosed": "Mathlib.Analysis.Complex.Polynomial.Basic",
            "LinearMap.rank_range_add_rank_ker": "Mathlib.LinearAlgebra.Dimension.RankNullity",
            "DivisionRing.hasRankNullity": "Mathlib.LinearAlgebra.Dimension.DivisionRing",
            "Sylow.exists_subgroup_card_pow_prime": "Mathlib.GroupTheory.Sylow",
            "Sylow.isPretransitive_of_finite": "Mathlib.GroupTheory.Sylow",
            "card_sylow_modEq_one": "Mathlib.GroupTheory.Sylow",
            "EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two":
                "Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle",
            "SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph":
                "Mathlib.Combinatorics.SimpleGraph.Extremal.Turan",
            "SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree":
                "Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits",
            "intervalIntegral.integral_hasDerivAt_right":
                "Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus",
            "intervalIntegral.integral_eq_sub_of_hasDerivAt":
                "Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus",
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                origin = self.catalog["sources"][module]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn("Authors:", origin["notice"])

    def test_landmark_hierarchies_reach_their_definitions_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "Complex.exists_root": {"Complex", "Real", "Polynomial", "Differentiable"},
            "intervalIntegral.integral_eq_sub_of_hasDerivAt":
                {"MeasureTheory.integral", "MeasureTheory.Measure", "MeasurableSpace", "HasDerivAt"},
            "EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two":
                {"Real", "InnerProductSpace", "MetricSpace", "NormedAddTorsor"},
            "SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph":
                {"SimpleGraph", "SimpleGraph.IsTuranMaximal", "SimpleGraph.turanGraph"},
            "SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree":
                {"SimpleGraph", "Real", "SimpleGraph.minDegree", "SimpleGraph.completeEquipartiteGraph"},
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_rank_nullity_is_proved_for_division_rings(self):
        theorem = self.nodes["LinearMap.rank_range_add_rank_ker"]
        self.assertIn("HasRankNullity", theorem["type_dependencies"])
        instance = self.nodes["DivisionRing.hasRankNullity"]
        self.assertEqual(instance["kind"], "theorem")
        self.assertIn("DivisionRing", instance["type_dependencies"])
        self.assertTrue(instance["value_dependencies"])
        self.assertTrue(set(instance["axioms"]) <= self.policy["axioms"].keys())

    def test_computability_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ComputabilityStatements.lean"], capture=True)

    def test_algebra_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/AlgebraStatements.lean"], capture=True)

    def test_number_theory_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/NumberTheoryStatements.lean"], capture=True)

    def test_pinned_bibliography_retains_every_source_byte_and_entry(self):
        bibliography = self.catalog["bibliographies"]["mathlib"]
        path = ROOT / ".lake/packages/mathlib" / self.policy["libraries"]["mathlib"]["bibliography"]
        data = path.read_bytes()
        self.assertEqual(bibliography["text"].encode(), data)
        self.assertEqual(bibliography["sha256"], hashlib.sha256(data).hexdigest())
        self.assertEqual(len(bibliography["entries"]), sum(line.startswith(b"@") for line in data.splitlines()))
        self.assertEqual(bibliography["revision"], self.policy["libraries"]["mathlib"]["revision"])
        self.assertEqual(bibliography["license"], "Apache-2.0")
        self.assertIn(bibliography["revision"], bibliography["url"])

    def test_mathematical_references_preserve_declaration_and_module_scopes(self):
        snapshot = open_snapshot(ROOT)
        pell = snapshot.citations("Pell.exists_of_not_isSquare")
        self.assertEqual(pell["declaration_citations"], [])
        self.assertIn("IrelandRosen1990", {item["key"] for item in pell["module_citations"]})
        name = "RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc"
        result = snapshot.citations(name)
        self.assertIn("marcus1977number", {item["key"] for item in result["declaration_citations"]})
        self.assertIn("marcus1977number", {item["key"] for item in result["module_citations"]})
        number_field = snapshot.citations("NumberField")
        self.assertTrue({"marcus1977number", "cassels1967algebraic", "samuel1967"} <=
                        {item["key"] for item in number_field["module_citations"]})

    def test_number_theory_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "ZMod": "Data.ZMod.Defs",
            "EuclideanDomain": "Algebra.EuclideanDomain.Defs",
            "quadraticChar": "NumberTheory.LegendreSymbol.QuadraticChar.Basic",
            "legendreSym": "NumberTheory.LegendreSymbol.Basic",
            "jacobiSym": "NumberTheory.LegendreSymbol.JacobiSymbol",
            "legendreSym.quadratic_reciprocity": "NumberTheory.LegendreSymbol.QuadraticReciprocity",
            "jacobiSym.quadratic_reciprocity": "NumberTheory.LegendreSymbol.JacobiSymbol",
            "Zsqrtd": "NumberTheory.Zsqrtd.Basic",
            "Pell.Solution₁": "NumberTheory.Pell",
            "Pell.IsFundamental": "NumberTheory.Pell",
            "Pell.exists_of_not_isSquare": "NumberTheory.Pell",
            "Pell.existsUnique_pos_generator": "NumberTheory.Pell",
            "IsIntegral": "RingTheory.IntegralClosure.IsIntegral.Defs",
            "Algebra.IsIntegral": "RingTheory.IntegralClosure.Algebra.Defs",
            "integralClosure": "RingTheory.IntegralClosure.Algebra.Basic",
            "IsIntegrallyClosed": "RingTheory.IntegralClosure.IntegrallyClosed",
            "FractionRing": "RingTheory.Localization.FractionRing",
            "IsFractionRing": "RingTheory.Localization.FractionRing",
            "FractionalIdeal": "RingTheory.FractionalIdeal.Basic",
            "ClassGroup": "RingTheory.ClassGroup.Basic",
            "IsDedekindDomain": "RingTheory.DedekindDomain.Basic",
            "Algebra.norm": "RingTheory.Norm.Defs",
            "Ideal.absNorm": "RingTheory.Ideal.Norm.AbsNorm",
            "Ideal.uniqueFactorizationMonoid": "RingTheory.DedekindDomain.Ideal.Basic",
            "Ideal.finprod_heightOneSpectrum_factorization": "RingTheory.DedekindDomain.Factorization",
            "FractionalIdeal.finprod_heightOneSpectrum_factorization'": "RingTheory.DedekindDomain.Factorization",
            "NumberField": "NumberTheory.NumberField.Basic",
            "NumberField.RingOfIntegers": "NumberTheory.NumberField.Basic",
            "NumberField.InfinitePlace": "NumberTheory.NumberField.InfinitePlace.Basic",
            "NumberField.FinitePlace": "NumberTheory.NumberField.Completion.FinitePlace",
            "NumberField.discr": "NumberTheory.NumberField.Discriminant.Defs",
            "NumberField.classNumber": "NumberTheory.NumberField.ClassNumber",
            "NumberField.classNumber_pos": "NumberTheory.NumberField.ClassNumber",
            "NumberField.classNumber_eq_one_iff": "NumberTheory.NumberField.ClassNumber",
            "NumberField.exists_ideal_in_class_of_norm_le": "NumberTheory.NumberField.ClassNumber",
            "NumberField.Units.torsion": "NumberTheory.NumberField.Units.Basic",
            "NumberField.Units.rank": "NumberTheory.NumberField.Units.DirichletTheorem",
            "NumberField.Units.finrank_modTorsion": "NumberTheory.NumberField.Units.DirichletTheorem",
            "NumberField.Units.basisModTorsion": "NumberTheory.NumberField.Units.DirichletTheorem",
            "NumberField.Units.exist_unique_eq_mul_prod": "NumberTheory.NumberField.Units.DirichletTheorem",
            "NumberField.Units.regulator": "NumberTheory.NumberField.Units.Regulator",
            "NumberField.Units.regulator_pos": "NumberTheory.NumberField.Units.Regulator",
            "NumberField.prod_abs_eq_one": "NumberTheory.NumberField.ProductFormula",
            "RingOfIntegers.exponent": "NumberTheory.NumberField.Ideal.KummerDedekind",
            "NumberField.Ideal.primesOverSpanEquivMonicFactorsMod": "NumberTheory.NumberField.Ideal.KummerDedekind",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], "Mathlib." + suffix)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][node["module"]]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_probability_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ProbabilityStatements.lean"], capture=True)

    def test_topology_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/TopologyStatements.lean"], capture=True)

    def test_topology_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "Path": "Topology.Path",
            "ZerothHomotopy": "Topology.Connected.PathConnected",
            "PathConnectedSpace": "Topology.Connected.PathConnected",
            "ContinuousMap.Homotopy": "Topology.Homotopy.Basic",
            "ContinuousMap.HomotopyRel": "Topology.Homotopy.Basic",
            "ContinuousMap.HomotopyEquiv": "Topology.Homotopy.Equiv",
            "ContractibleSpace": "Topology.Homotopy.Contractible",
            "SimplyConnectedSpace": "AlgebraicTopology.FundamentalGroupoid.SimplyConnected",
            "SimplyConnectedSpace.ofContractible": "AlgebraicTopology.FundamentalGroupoid.SimplyConnected",
            "FundamentalGroupoid": "AlgebraicTopology.FundamentalGroupoid.Basic",
            "FundamentalGroup": "AlgebraicTopology.FundamentalGroupoid.FundamentalGroup",
            "FundamentalGroup.fundamentalGroupMulEquivOfPathConnected": "AlgebraicTopology.FundamentalGroupoid.FundamentalGroup",
            "HomotopyGroup": "Topology.Homotopy.HomotopyGroup",
            "HomotopyGroup.commGroup": "Topology.Homotopy.HomotopyGroup",
            "EckmannHilton.mul_comm": "GroupTheory.EckmannHilton",
            "HomotopyGroup.pi0EquivZerothHomotopy": "Topology.Homotopy.HomotopyGroup",
            "HomotopyGroup.pi1MulEquivFundamentalGroup": "Topology.Homotopy.HomotopyGroup",
            "IsCoveringMap": "Topology.Covering.Basic",
            "IsQuotientCoveringMap": "Topology.Covering.Quotient",
            "IsQuotientCoveringMap.fundamentalGroupEquiv": "Topology.Homotopy.Lifting",
            "deck": "Topology.Covering.Deck",
            "AddCircle.zsmulLoop": "Topology.Covering.FundamentalGroupCircle",
            "AddCircle.windingNumberIso": "Topology.Covering.FundamentalGroupCircle",
            "AddCircle.windingNumber": "Topology.Covering.FundamentalGroupCircle",
            "AddCircle.windingNumber_eq_div": "Topology.Covering.FundamentalGroupCircle",
            "AddCircle.windingNumber_zsmulLoop": "Topology.Covering.FundamentalGroupCircle",
            "TopCat": "Topology.Category.TopCat.Basic",
            "TopCat.Homotopy": "Topology.Homotopy.TopCat.Basic",
            "SSet": "AlgebraicTopology.SimplicialSet.Basic",
            "CategoryTheory.SimplicialObject": "AlgebraicTopology.SimplicialObject.Basic",
            "TopCat.toSSet": "AlgebraicTopology.SingularSet",
            "SSet.toTop": "AlgebraicTopology.SingularSet",
            "sSetTopAdj": "AlgebraicTopology.SingularSet",
            "HomologicalComplex": "Algebra.Homology.HomologicalComplex",
            "ChainComplex": "Algebra.Homology.HomologicalComplex",
            "CategoryTheory.ShortComplex": "Algebra.Homology.ShortComplex.Basic",
            "CategoryTheory.CategoryWithHomology": "Algebra.Homology.ShortComplex.Homology",
            "HomologicalComplex.homologyFunctor": "Algebra.Homology.ShortComplex.HomologicalComplex",
            "Homotopy": "Algebra.Homology.Homotopy",
            "Homotopy.homologyMap_eq": "Algebra.Homology.Homotopy",
            "AlgebraicTopology.singularChainComplexFunctor": "AlgebraicTopology.SingularHomology.Basic",
            "AlgebraicTopology.singularHomologyFunctor": "AlgebraicTopology.SingularHomology.Basic",
            "AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace": "AlgebraicTopology.SingularHomology.Basic",
            "TopCat.singularHomology₀Iso": "AlgebraicTopology.SingularHomology.HomologyZero",
            "TopCat.Homotopy.singularChainComplexFunctorObjMap": "AlgebraicTopology.SingularHomology.HomotopyInvariance",
            "TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor": "AlgebraicTopology.SingularHomology.HomotopyInvariance",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], "Mathlib." + suffix)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][node["module"]]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_topology_hierarchies_reach_models_assumptions_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "AddCircle.windingNumberIso":
                {"FundamentalGroup", "AddCircle", "Int", "SimplyConnectedSpace", "IsAddQuotientCoveringMap"},
            "AddCircle.windingNumber_zsmulLoop":
                {"AddCircle.zsmulLoop", "AddCircle.windingNumber", "Path", "FundamentalGroup"},
            "HomotopyGroup.commGroup":
                {"HomotopyGroup", "GenLoop", "ContinuousMap.HomotopyRel", "EckmannHilton.mul_comm"},
            "SimplyConnectedSpace.ofContractible":
                {"ContractibleSpace", "SimplyConnectedSpace", "FundamentalGroupoid", "ContinuousMap.HomotopyEquiv"},
            "IsQuotientCoveringMap.fundamentalGroupEquiv":
                {"IsQuotientCoveringMap", "FundamentalGroup", "SimplyConnectedSpace", "MulOpposite"},
            "sSetTopAdj": {"SSet.toTop", "TopCat.toSSet", "CategoryTheory.Adjunction", "SimplexCategory"},
            "TopCat.singularHomology₀Iso":
                {"AlgebraicTopology.singularHomologyFunctor", "ZerothHomotopy",
                 "HomologicalComplex.homologyFunctor", "CategoryTheory.CategoryWithHomology"},
            "TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor":
                {"TopCat.Homotopy", "Homotopy", "AlgebraicTopology.singularChainComplexFunctor",
                 "HomologicalComplex.homologyMap", "CategoryTheory.CategoryWithHomology"},
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_topology_subjects_include_their_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "algebraic_topology": ("topology", "AddCircle.windingNumberIso"),
            "fundamental_groups": ("algebraic_topology", "FundamentalGroup"),
            "homotopy_theory": ("algebraic_topology", "HomotopyGroup.commGroup"),
            "covering_spaces": ("algebraic_topology", "AddCircle.windingNumberIso"),
            "simplicial_topology": ("algebraic_topology", "sSetTopAdj"),
            "homology": ("algebraic_topology", "TopCat.singularHomology₀Iso"),
            "homological_algebra": ("algebra", "Homotopy.homologyMap_eq"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_model_theory_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ModelTheoryStatements.lean"], capture=True)

    def test_model_theory_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "FirstOrder.Language": "Basic",
            "FirstOrder.Language.Structure": "Basic",
            "FirstOrder.Language.Term": "Syntax",
            "FirstOrder.Language.BoundedFormula": "Syntax",
            "FirstOrder.Language.Formula": "Syntax",
            "FirstOrder.Language.Sentence": "Syntax",
            "FirstOrder.Language.Theory": "Syntax",
            "FirstOrder.Language.BoundedFormula.Realize": "Semantics",
            "FirstOrder.Language.BoundedFormula.realize_subst": "Semantics",
            "FirstOrder.Language.Theory.Model": "Semantics",
            "FirstOrder.Language.completeTheory": "Semantics",
            "FirstOrder.Language.ElementarilyEquivalent": "Semantics",
            "FirstOrder.Language.BoundedFormula.IsQF": "Complexity",
            "FirstOrder.Language.BoundedFormula.IsPrenex": "Complexity",
            "FirstOrder.Language.BoundedFormula.toPrenex": "Complexity",
            "FirstOrder.Language.BoundedFormula.realize_toPrenex": "Complexity",
            "FirstOrder.Language.Substructure": "Substructures",
            "FirstOrder.Language.ElementaryEmbedding": "ElementaryMaps",
            "FirstOrder.Language.elementaryDiagram": "ElementaryMaps",
            "FirstOrder.Language.ElementarySubstructure": "ElementarySubstructures",
            "FirstOrder.Language.Substructure.isElementary_of_exists": "ElementarySubstructures",
            "FirstOrder.Language.Theory.IsSatisfiable": "Satisfiability",
            "FirstOrder.Language.Theory.IsFinitelySatisfiable": "Satisfiability",
            "FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable": "Satisfiability",
            "FirstOrder.Language.Theory.models_iff_finset_models": "Satisfiability",
            "FirstOrder.Language.Theory.IsComplete": "Satisfiability",
            "FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_ge": "Satisfiability",
            "FirstOrder.Language.exists_elementarySubstructure_card_eq": "Skolem",
            "FirstOrder.Language.Ultraproduct.sentence_realize": "Ultraproducts",
            "FirstOrder.Language.IsFraisse": "Fraisse",
            "FirstOrder.Language.IsFraisseLimit": "Fraisse",
            "FirstOrder.Language.IsFraisseLimit.nonempty_equiv": "Fraisse",
            "Set.Definable": "Definability",
            "FirstOrder.Language.Theory.CompleteType": "Types",
            "FirstOrder.Language.Theory.CompleteType.nonempty_iff": "Types",
            "FirstOrder.Language.Theory.exists_modelType_is_realized_in": "Types",
            "CompleteType.isClopen_typesWith": "Topology.Types",
            "FirstOrder.Language.ring": "Algebra.Ring.Basic",
            "FirstOrder.Language.Theory.ACF": "Algebra.Field.IsAlgClosed",
            "FirstOrder.Field.ACF_isComplete": "Algebra.Field.IsAlgClosed",
            "FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize": "Algebra.Field.IsAlgClosed",
            "FirstOrder.Field.ACF_zero_realize_iff_finite_ACF_prime_not_realize": "Algebra.Field.IsAlgClosed",
            "FirstOrder.Language.presburger": "Arithmetic.Presburger.Basic",
            "IsSemilinearSet": "Arithmetic.Presburger.Semilinear.Defs",
            "FirstOrder.Language.presburger.definable_iff_isSemilinearSet": "Arithmetic.Presburger.Definability",
            "FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic": "Arithmetic.Presburger.Definability",
            "FirstOrder.Language.presburger.mul_not_definable": "Arithmetic.Presburger.Definability",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], "Mathlib.ModelTheory." + suffix)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][node["module"]]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_model_theory_hierarchies_reach_models_assumptions_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable": {
                "FirstOrder.Language.Ultraproduct.sentence_realize",
                "FirstOrder.Language.Theory.IsSatisfiable",
                "FirstOrder.Language.Theory.IsFinitelySatisfiable",
            },
            "FirstOrder.Language.Ultraproduct.sentence_realize": {
                "FirstOrder.Language.BoundedFormula.Realize",
                "Quotient",
            },
            "FirstOrder.Language.exists_elementarySubstructure_card_eq": {
                "FirstOrder.Language.ElementarySubstructure",
                "FirstOrder.Language.Substructure",
            },
            "FirstOrder.Language.exists_elementaryEmbedding_card_eq_of_ge": {
                "FirstOrder.Language.ElementaryEmbedding",
                "FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable",
            },
            "FirstOrder.Field.ACF_isComplete": {
                "FirstOrder.Language.Theory.ACF",
                "FirstOrder.Language.Theory.IsComplete",
                "IsAlgClosed",
            },
            "FirstOrder.Field.ACF_zero_realize_iff_finite_ACF_prime_not_realize": {
                "FirstOrder.Language.Theory.ACF",
                "FirstOrder.Field.ACF_isComplete",
                "FirstOrder.Language.Theory.models_iff_finset_models",
            },
            "FirstOrder.Language.presburger.definable_iff_isSemilinearSet": {
                "FirstOrder.Language.presburger",
                "Set.Definable",
                "IsSemilinearSet",
            },
            "FirstOrder.Language.presburger.mul_not_definable": {
                "FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic",
            },
            "FirstOrder.Language.IsFraisseLimit.nonempty_equiv": {
                "FirstOrder.Language.IsFraisseLimit",
                "FirstOrder.Language.PartialEquiv",
            },
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_model_theory_subjects_include_their_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "first_order_logic": ("logic", "FirstOrder.Language.BoundedFormula"),
            "model_theory": ("first_order_logic", "FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable"),
            "types_and_definability": ("model_theory", "FirstOrder.Language.Theory.CompleteType"),
            "algebraic_model_theory": ("model_theory", "FirstOrder.Field.ACF_isComplete"),
            "presburger_arithmetic": ("first_order_logic", "FirstOrder.Language.presburger.mul_not_definable"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_model_theory_references_link_their_pinned_records(self):
        snapshot = open_snapshot(ROOT)
        expected = {
            "FirstOrder.Language": {"flypitch_cpp", "flypitch_itp"},
            "FirstOrder.Language.presburger.definable_iff_isSemilinearSet":
                {"ginsburg1964", "ginsburg1966", "eilenberg1969"},
        }
        for name, keys in expected.items():
            with self.subTest(name=name):
                references = snapshot.citations(name)
                self.assertTrue(keys <= {entry["key"] for entry in references["module_citations"]})

    def test_set_theory_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/SetTheoryStatements.lean"], capture=True)

    def test_set_theory_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "PSet": "ZFC.PSet",
            "PSet.Equiv": "ZFC.PSet",
            "PSet.omega": "ZFC.PSet",
            "ZFSet": "ZFC.Basic",
            "ZFSet.Definable": "ZFC.Basic",
            "ZFSet.sep": "ZFC.Basic",
            "ZFSet.ext": "ZFC.Basic",
            "ZFSet.powerset": "ZFC.Basic",
            "ZFSet.omega": "ZFC.Basic",
            "ZFSet.omega_zero": "ZFC.Basic",
            "ZFSet.omega_succ": "ZFC.Basic",
            "ZFSet.regularity": "ZFC.Basic",
            "ZFSet.mem_image": "ZFC.Basic",
            "ZFSet.choice": "ZFC.Class",
            "ZFSet.choice_isFunc": "ZFC.Class",
            "ZFSet.choice_cmem": "ZFC.Class",
            "ZFClass": "ZFC.Class",
            "ZFClass.CMem": "ZFC.Class",
            "ZFSet.isOrdinal_notCMem_univ": "ZFC.Class",
            "Classical.allZFSetDefinable": "ZFC.Basic",
            "ZFSet.IsOrdinal": "ZFC.Ordinal",
            "Ordinal.toZFSet": "ZFC.Ordinal",
            "Ordinal.toZFSetIso": "ZFC.Ordinal",
            "Ordinal.rank_toZFSet": "ZFC.Ordinal",
            "ZFSet.rank": "ZFC.Rank",
            "ZFSet.rank_lt_of_mem": "ZFC.Rank",
            "ZFSet.card": "ZFC.Cardinal",
            "ZFSet.card_powerset": "ZFC.Cardinal",
            "ZFSet.vonNeumann": "ZFC.VonNeumann",
            "ZFSet.mem_vonNeumann": "ZFC.VonNeumann",
            "ZFSet.vonNeumann_add_one": "ZFC.VonNeumann",
            "ZFSet.exists_mem_vonNeumann": "ZFC.VonNeumann",
            "ZFSet.card_vonNeumann": "ZFC.VonNeumann",
            "Ordinal": "Ordinal.Basic",
            "Ordinal.instPow": "Ordinal.Exponential",
            "Ordinal.CNF": "Ordinal.CantorNormalForm",
            "Ordinal.CNF.foldr": "Ordinal.CantorNormalForm",
            "Ordinal.nfp": "Ordinal.FixedPoint",
            "Ordinal.deriv": "Ordinal.FixedPoint",
            "Ordinal.veblen": "Ordinal.Veblen",
            "Ordinal.gamma": "Ordinal.Veblen",
            "Ordinal.omega0_opow_epsilon": "Ordinal.Veblen",
            "Ordinal.epsilon_zero_le_of_omega0_opow_le": "Ordinal.Veblen",
            "Ordinal.IsFundamentalSeq": "Ordinal.FundamentalSequence",
            "Ordinal.exists_isFundamentalSeq": "Ordinal.FundamentalSequence",
            "ONote": "Ordinal.Notation",
            "ONote.NF": "Ordinal.Notation",
            "NONote": "Ordinal.Notation",
            "ONote.repr_add": "Ordinal.Notation",
            "ONote.repr_mul": "Ordinal.Notation",
            "ONote.repr_opow": "Ordinal.Notation",
            "Cardinal": "Cardinal.Defs",
            "Cardinal.cantor": "Cardinal.Order",
            "Cardinal.add_eq_self": "Cardinal.Arithmetic",
            "Cardinal.mul_eq_self": "Cardinal.Arithmetic",
            "Cardinal.aleph": "Cardinal.Aleph",
            "Cardinal.beth": "Cardinal.Aleph",
            "Cardinal.preBeth": "Cardinal.Aleph",
            "Cardinal.continuum": "Cardinal.Continuum",
            "Cardinal.beth_one": "Cardinal.Continuum",
            "Cardinal.IsRegular": "Cardinal.Regular",
            "Cardinal.IsSingular": "Cardinal.Regular",
            "Cardinal.IsInaccessible": "Cardinal.Regular",
            "Cardinal.isRegular_aleph_add_one": "Cardinal.Regular",
            "Order.cof": "Cardinal.Cofinality.Basic",
            "Ordinal.cof": "Cardinal.Cofinality.Ordinal",
            "IsClub": "Cardinal.Cofinality.Club",
            "IsStationary": "Cardinal.Cofinality.Club",
            "exists_isStationary_preimage_singleton": "Cardinal.Cofinality.Club",
            "Lists": "Lists",
            "Lists'": "Lists",
            "Descriptive.tree": "Descriptive.Tree",
            "Descriptive.Tree.mem_of_prefix": "Descriptive.Tree",
            "Descriptive.Tree.pullSub_adjunction": "Descriptive.Tree",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], "Mathlib.SetTheory." + suffix)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][node["module"]]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_set_theory_hierarchies_reach_models_assumptions_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "ZFSet.regularity": {
                "PSet",
                "Quotient",
                "WellFounded",
            },
            "ZFSet.choice_isFunc": {
                "Classical.choice",
                "Classical.allZFSetDefinable",
                "ZFSet.IsFunc",
                "ZFSet.map",
                "ZFSet.choice",
            },
            "ZFSet.isOrdinal_notCMem_univ": {
                "ZFSet.IsOrdinal",
                "ZFClass.CMem",
                "ZFClass.cmem_irrefl",
            },
            "Ordinal.toZFSetIso": {
                "ZFSet.IsOrdinal",
                "ZFSet.rank",
                "Ordinal.toZFSet",
            },
            "ZFSet.card_vonNeumann": {
                "ZFSet.vonNeumann",
                "Cardinal.preBeth",
                "ZFSet.card",
                "Ordinal.limitRecOn",
            },
            "Ordinal.CNF.foldr": {
                "Ordinal.CNF",
                "Ordinal.instPow",
            },
            "ONote.repr_opow": {
                "ONote.repr",
                "ONote.NF",
                "ONote.opow",
                "Ordinal.instPow",
            },
            "Ordinal.omega0_opow_epsilon": {
                "Ordinal.veblen",
                "Ordinal.deriv",
                "Ordinal.deriv_fp",
            },
            "exists_isStationary_preimage_singleton": {
                "IsClub.diag",
                "IsStationary",
                "Order.cof",
                "Classical.choice",
            },
            "Cardinal.beth_one": {
                "Cardinal.beth",
                "Cardinal.continuum",
                "Cardinal.beth_succ",
            },
            "Ordinal.exists_isFundamentalSeq": {
                "Ordinal.IsFundamentalSeq",
                "Order.cof",
                "Ordinal.cof",
            },
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_set_theory_subjects_include_their_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "cardinal_numbers": ("set_theory", "Cardinal"),
            "cardinal_arithmetic": ("cardinal_numbers", "Cardinal.add_eq_self"),
            "cofinality": ("cardinal_numbers", "exists_isStationary_preimage_singleton"),
            "ordinals": ("set_theory", "Ordinal"),
            "ordinal_arithmetic": ("ordinals", "Ordinal.CNF.foldr"),
            "ordinal_notation": ("ordinal_arithmetic", "ONote.repr_opow"),
            "zfc_sets": ("set_theory", "ZFSet.choice_isFunc"),
            "finite_set_models": ("set_theory", "Lists"),
            "set_theoretic_trees": ("set_theory", "Descriptive.tree"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_set_theory_references_link_their_pinned_records(self):
        snapshot = open_snapshot(ROOT)
        references = snapshot.citations("Ordinal.veblen")
        self.assertIn("Miller_1976", {entry["key"] for entry in references["module_citations"]})

    def test_prime_progression_results_retain_local_proofs_and_source(self):
        expected = {
            "Math.NumberTheory.prime_eq_gcd_of_not_coprime": "theorem",
            "Math.NumberTheory.finite_primes_modEq_of_not_coprime": "theorem",
            "Math.NumberTheory.infinite_primes_modEq_iff": "theorem",
            "Math.NumberTheory.infinite_primes_modEq_above_avoiding_iff": "theorem",
            "Math.NumberTheory.exists_prime_modEq_above_avoiding": "theorem",
            "Math.NumberTheory.exists_finset_primes_modEq_card": "theorem",
            "Math.NumberTheory.forall_finset_exists_prime_modEq_iff": "theorem"
        }
        module = "Math.NumberTheory.PrimeProgressions"
        path = ROOT / "Math/NumberTheory/PrimeProgressions.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name, kind in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                node = self.nodes[name]
                self.assertEqual(node["kind"], kind)
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ('primes_in_progressions', 'analytic_number_theory', 'number_theory', 'mathematics'):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_sturm_finite_results_retain_local_proofs_and_source(self):
        expected = {
            "Math.NumberTheory.modularForm_eq_zero_iff_coeffs": "theorem",
            "Math.NumberTheory.modularForm_eq_iff_coeffs": "theorem",
            "Math.NumberTheory.sturmCoefficients_injective": "theorem",
            "Math.NumberTheory.sturmCoefficients": "definition"
        }
        module = "Math.NumberTheory.SturmFinite"
        path = ROOT / "Math/NumberTheory/SturmFinite.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name, kind in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                node = self.nodes[name]
                self.assertEqual(node["kind"], kind)
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ('modular_identity_certificates', 'modular_forms', 'analytic_number_theory', 'number_theory', 'mathematics'):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_fitting_naturality_statements_match_independent_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/FittingNaturalStatements.lean"], capture=True)

    def test_fitting_naturality_results_retain_local_terms_and_source(self):
        expected = {'Math.LinearAlgebra.intertwines_pow': 'theorem',
         'Math.LinearAlgebra.maps_fittingKer': 'theorem',
         'Math.LinearAlgebra.maps_fittingRange': 'theorem',
         'Math.LinearAlgebra.mapFittingKer': 'definition',
         'Math.LinearAlgebra.mapFittingRange': 'definition',
         'Math.LinearAlgebra.fittingEquiv_natural': 'theorem',
         'Math.LinearAlgebra.fittingProjection_natural': 'theorem',
         'Math.LinearAlgebra.comp_fittingProjection': 'theorem'}
        module = "Math.Algebra.FittingNatural"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], "Math/Algebra/FittingNatural.lean")
        self.assertEqual(origin["sha256"], hashlib.sha256((ROOT / origin["path"]).read_bytes()).hexdigest())
        for name, kind in expected.items():
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                self.assertEqual(node["module"], module)
                self.assertEqual(node["kind"], kind)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))

    def test_fitting_statements_match_independent_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/FittingStatements.lean"], capture=True)

    def test_linear_algebra_statements_match_independent_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/LinearAlgebraStatements.lean"], capture=True)

    def test_linear_algebra_registry_retains_the_complete_pinned_family(self):
        base = ROOT / ".lake/packages/mathlib"
        registered = self.policy["libraries"]["mathlib"]["modules"]
        expected = {".".join(path.relative_to(base).with_suffix("").parts)
                    for path in (base / "Mathlib/LinearAlgebra").rglob("*.lean")}
        self.assertEqual(len(expected), 386)
        self.assertEqual({name for name in registered if name.startswith("Mathlib.LinearAlgebra.")}, expected)
        for module in expected:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                origin = self.catalog["sources"][module]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertEqual(origin["license"], "Apache-2.0")
                self.assertEqual(origin["sha256"], hashlib.sha256(
                    (base / (module.replace(".", "/") + ".lean")).read_bytes()).hexdigest())

    def test_fitting_results_retain_local_proofs_and_source(self):
        expected = {'Math.LinearAlgebra.range_pow_eq_finrank': 'theorem',
         'Math.LinearAlgebra.isCompl_pow_finrank': 'theorem',
         'Math.LinearAlgebra.fittingEquiv': 'definition',
         'Math.LinearAlgebra.fittingEquiv_apply': 'theorem',
         'Math.LinearAlgebra.existsUnique_fitting': 'theorem',
         'Math.LinearAlgebra.isNilpotent_iff_pow_finrank': 'theorem',
         'Math.LinearAlgebra.fittingKer_invariant': 'theorem',
         'Math.LinearAlgebra.fittingRange_invariant': 'theorem',
         'Math.LinearAlgebra.fittingNilpotent': 'definition',
         'Math.LinearAlgebra.fittingNilpotent_pow': 'theorem',
         'Math.LinearAlgebra.fittingInvertible': 'definition',
         'Math.LinearAlgebra.fittingInvertible_isUnit': 'theorem',
         'Math.LinearAlgebra.fittingEquiv_intertwines': 'theorem',
         'Math.LinearAlgebra.fittingProjection': 'definition',
         'Math.LinearAlgebra.range_fittingProjection': 'theorem',
         'Math.LinearAlgebra.ker_fittingProjection': 'theorem',
         'Math.LinearAlgebra.fittingProjection_idempotent': 'theorem',
         'Math.LinearAlgebra.fittingProjection_apply_add': 'theorem',
         'Math.LinearAlgebra.fittingKer_invariant_of_commute': 'theorem',
         'Math.LinearAlgebra.fittingRange_invariant_of_commute': 'theorem',
         'Math.LinearAlgebra.fittingProjection_commutes': 'theorem',
         'Math.LinearAlgebra.fittingProjection_mul_pow': 'theorem',
         'Math.LinearAlgebra.pow_mul_fittingProjection': 'theorem'}
        module = "Math.Algebra.FittingFinite"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], "Math/Algebra/FittingFinite.lean")
        self.assertEqual(origin["sha256"], hashlib.sha256((ROOT / origin["path"]).read_bytes()).hexdigest())
        for name, kind in expected.items():
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                self.assertEqual(node["module"], module)
                self.assertEqual(node["kind"], kind)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))

    def test_linear_algebra_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {'Matrix.det_mul': 'Mathlib.LinearAlgebra.Matrix.Determinant.Basic',
         'Matrix.det_one': 'Mathlib.LinearAlgebra.Matrix.Determinant.Basic',
         'Matrix.det_transpose': 'Mathlib.LinearAlgebra.Matrix.Determinant.Basic',
         'LinearMap.charpoly': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.charpoly_monic': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.aeval_self_charpoly': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.isIntegral': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.aeval_eq_aeval_mod_charpoly': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.pow_eq_aeval_mod_charpoly': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.charpoly_natDegree': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.charpoly_sub_smul': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'LinearMap.minpoly_dvd_charpoly': 'Mathlib.LinearAlgebra.Charpoly.Basic',
         'Module.End.hasEigenvalue_iff_isRoot_charpoly': 'Mathlib.LinearAlgebra.Eigenspace.Charpoly',
         'Module.End.mem_spectrum_iff_isRoot_charpoly': 'Mathlib.LinearAlgebra.Eigenspace.Charpoly',
         'LinearMap.finrank_range_add_finrank_ker': 'Mathlib.LinearAlgebra.FiniteDimensional.Lemmas',
         'Module.End.exists_isNilpotent_isSemisimple': 'Mathlib.LinearAlgebra.JordanChevalley',
         'Module.End.isNilpotent_isSemisimple_unique': 'Mathlib.LinearAlgebra.JordanChevalley',
         'Module.evalEquiv': 'Mathlib.LinearAlgebra.Dual.Defs',
         'Subspace.finrank_add_finrank_dualAnnihilator_eq': 'Mathlib.LinearAlgebra.Dual.Lemmas',
         'Module.Basis.tensorProduct': 'Mathlib.LinearAlgebra.TensorProduct.Basis',
         'Module.Basis.tensorProduct_apply': 'Mathlib.LinearAlgebra.TensorProduct.Basis',
         'Module.finrank_tensorProduct': 'Mathlib.LinearAlgebra.Dimension.Constructions',
         'TensorProduct': 'Mathlib.LinearAlgebra.TensorProduct.Defs',
         'CliffordAlgebra': 'Mathlib.LinearAlgebra.CliffordAlgebra.Basic',
         'CliffordAlgebra.ι': 'Mathlib.LinearAlgebra.CliffordAlgebra.Basic',
         'CliffordAlgebra.lift': 'Mathlib.LinearAlgebra.CliffordAlgebra.Basic',
         'CliffordAlgebra.ι_sq_scalar': 'Mathlib.LinearAlgebra.CliffordAlgebra.Basic',
         'CliffordAlgebra.ι_mul_ι_add_swap': 'Mathlib.LinearAlgebra.CliffordAlgebra.Basic',
         'CliffordAlgebra.ι_comp_lift': 'Mathlib.LinearAlgebra.CliffordAlgebra.Basic',
         'ExteriorAlgebra': 'Mathlib.LinearAlgebra.ExteriorAlgebra.Basic',
         'ExteriorAlgebra.ι_sq_zero': 'Mathlib.LinearAlgebra.ExteriorAlgebra.Basic',
         'ExteriorAlgebra.ι_add_mul_swap': 'Mathlib.LinearAlgebra.ExteriorAlgebra.Basic',
         'ExteriorAlgebra.lift': 'Mathlib.LinearAlgebra.ExteriorAlgebra.Basic',
         'ExteriorAlgebra.ι_comp_lift': 'Mathlib.LinearAlgebra.ExteriorAlgebra.Basic',
         'Projectivization': 'Mathlib.LinearAlgebra.Projectivization.Basic',
         'Projectivization.mk_eq_mk_iff': 'Mathlib.LinearAlgebra.Projectivization.Basic',
         "Projectivization.mk_eq_mk_iff'": 'Mathlib.LinearAlgebra.Projectivization.Basic',
         'RootPairing': 'Mathlib.LinearAlgebra.RootSystem.Defs',
         'RootPairing.weylGroup': 'Mathlib.LinearAlgebra.RootSystem.WeylGroup',
         'RootPairing.reflection_mem_weylGroup': 'Mathlib.LinearAlgebra.RootSystem.WeylGroup',
         'RootPairing.IsG2': 'Mathlib.LinearAlgebra.RootSystem.Finite.G2',
         'RootPairing.isG2_iff': 'Mathlib.LinearAlgebra.RootSystem.Finite.G2',
         'sigPos': 'Mathlib.LinearAlgebra.QuadraticForm.Signature',
         'sigPos_le_finrank': 'Mathlib.LinearAlgebra.QuadraticForm.Signature',
         'exists_finrank_eq_sigPos_and_posDef': 'Mathlib.LinearAlgebra.QuadraticForm.Signature',
         'SymmetricAlgebra': 'Mathlib.LinearAlgebra.SymmetricAlgebra.Basic',
         'SymmetricAlgebra.lift': 'Mathlib.LinearAlgebra.SymmetricAlgebra.Basic',
         'AffineMap': 'Mathlib.LinearAlgebra.AffineSpace.AffineMap',
         'AffineMap.homothety_apply': 'Mathlib.LinearAlgebra.AffineSpace.AffineMap'}
        for name, module in expected.items():
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertIn(name, self.catalog["roots"])
                self.assertEqual(node["module"], module)
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertIn(origin["revision"], origin["url"])

    def test_linear_algebra_hierarchies_retain_hypotheses_and_complete_axiom_paths(self):
        expected = {'Math.LinearAlgebra.fittingEquiv': ['Math.LinearAlgebra.isCompl_pow_finrank',
                                             'Math.LinearAlgebra.range_pow_eq_finrank',
                                             'LinearMap.ker',
                                             'LinearMap.range',
                                             'FiniteDimensional',
                                             'DivisionRing'],
         'Math.LinearAlgebra.isNilpotent_iff_pow_finrank': ['IsNilpotent',
                                                            'Module.End.ker_pow_le_ker_pow_finrank',
                                                            'FiniteDimensional'],
         'Math.LinearAlgebra.fittingInvertible_isUnit': ['Math.LinearAlgebra.isCompl_pow_finrank',
                                                         'Math.LinearAlgebra.fittingRange_invariant',
                                                         'LinearMap.ker',
                                                         'IsUnit'],
         'Math.LinearAlgebra.fittingEquiv_intertwines': ['Math.LinearAlgebra.fittingEquiv',
                                                         'Math.LinearAlgebra.fittingNilpotent',
                                                         'Math.LinearAlgebra.fittingInvertible'],
         'Module.End.exists_isNilpotent_isSemisimple': ['PerfectField',
                                                        'FiniteDimensional',
                                                        'IsNilpotent',
                                                        'Module.End.IsSemisimple',
                                                        'Algebra.adjoin'],
         'LinearMap.aeval_self_charpoly': ['LinearMap.charpoly', 'Module.Free', 'Module.Finite', 'CommRing'],
         'RootPairing.reflection_mem_weylGroup': ['RootPairing.weylGroup', 'Subgroup.closure'],
         'Math.LinearAlgebra.fittingProjection_commutes': ['Math.LinearAlgebra.fittingProjection',
                                                           'Math.LinearAlgebra.fittingEquiv',
                                                           'Math.LinearAlgebra.fittingKer_invariant_of_commute',
                                                           'Math.LinearAlgebra.fittingRange_invariant_of_commute',
                                                           'Commute'],
         'Math.LinearAlgebra.fittingProjection_natural': ['Math.LinearAlgebra.fittingProjection',
                                                          'Math.LinearAlgebra.mapFittingKer',
                                                          'Math.LinearAlgebra.mapFittingRange',
                                                          'Math.LinearAlgebra.maps_fittingKer',
                                                          'Math.LinearAlgebra.maps_fittingRange',
                                                          'FiniteDimensional'],
         'Math.LinearAlgebra.maps_fittingRange': ['Math.LinearAlgebra.range_pow_eq_finrank',
                                                  'Math.LinearAlgebra.intertwines_pow',
                                                  'LinearMap.range']}
        graph = KnowledgeGraph(self.catalog)
        for name, required in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(required) <= reached, set(required) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for parent, child in zip(path, path[1:]):
                        self.assertIn(child, self.nodes[parent]["dependencies"])

    def test_linear_algebra_subjects_preserve_algebra_and_geometry_classifications(self):
        graph = KnowledgeGraph(self.catalog)
        parents = {
            "matrices": "linear_algebra", "characteristic_polynomials": "linear_algebra",
            "eigenspaces": "linear_algebra", "linear_operator_decomposition": "linear_algebra",
            "linear_dimension": "linear_algebra", "linear_bases": "linear_algebra",
            "finite_free_modules": "linear_algebra", "bilinear_forms": "linear_algebra",
            "quadratic_forms": "linear_algebra", "tensor_products": "linear_algebra",
            "multilinear_algebra": "linear_algebra", "exterior_algebra": "multilinear_algebra",
            "clifford_algebras": "linear_algebra", "symmetric_algebras": "multilinear_algebra",
            "affine_geometry": "geometry", "projective_spaces": "geometry",
            "root_systems": "linear_algebra", "linear_projections": "linear_algebra",
            "linear_groups": "linear_algebra", "module_direct_sums": "linear_algebra",
            "dual_spaces": "functional_analysis"
        }
        for subject, parent in parents.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                self.assertTrue(self.catalog["subjects"][subject]["modules"])
        expected = {'Matrix.det_mul': ['matrices', 'linear_algebra', 'algebra'],
         'LinearMap.aeval_self_charpoly': ['characteristic_polynomials', 'linear_algebra'],
         'Math.LinearAlgebra.fittingEquiv': ['linear_operator_decomposition', 'linear_projections', 'algebra'],
         'Math.LinearAlgebra.fittingProjection_commutes': ['linear_operator_decomposition',
                                                           'linear_projections',
                                                           'algebra'],
         'CliffordAlgebra.lift': ['clifford_algebras', 'linear_algebra'],
         'ExteriorAlgebra.lift': ['exterior_algebra', 'multilinear_algebra', 'algebra'],
         'SymmetricAlgebra.lift': ['symmetric_algebras', 'multilinear_algebra'],
         'Projectivization.mk_eq_mk_iff': ['projective_spaces', 'geometry'],
         'AffineMap.homothety_apply': ['affine_geometry', 'geometry'],
         'RootPairing.weylGroup': ['root_systems', 'linear_algebra'],
         'Math.LinearAlgebra.fittingProjection_natural': ['linear_operator_decomposition',
                                                          'linear_projections',
                                                          'algebra']}
        for name, subjects in expected.items():
            for subject in [*subjects, "mathematics"]:
                with self.subTest(name=name, subject=subject):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_miu_statements_match_independent_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/MiuStatements.lean"], capture=True)

    def test_miu_results_retain_complete_terms_and_local_source(self):
        expected = {
            "Math.Miu.countI": "definition",
            "Math.Miu.countI_mod_three": "theorem",
            "Math.Miu.mu_not_derivable": "theorem",
            "Math.Miu.theorem1": "theorem",
            "Math.Miu.pureI": "definition",
            "Math.Miu.pure_pow_two": "theorem",
            "Math.Miu.pure_drop_three": "theorem",
            "Math.Miu.pure_reduce": "theorem",
            "Math.Miu.pow_two_even_mod_three": "theorem",
            "Math.Miu.pow_two_odd_mod_three": "theorem",
            "Math.Miu.pure_of_mod_three": "theorem",
            "Math.Miu.expansionCost": "definition",
            "Math.Miu.expansionCost_mod_three": "theorem",
            "Math.Miu.realize_body": "theorem",
            "Math.Miu.body_of_mod_three": "theorem",
            "Math.Miu.countM": "definition",
            "Math.Miu.countM_eq_one": "theorem",
            "Math.Miu.head_eq_M": "theorem",
            "Math.Miu.derivable_iff": "theorem",
            "Math.Miu.Symbol": "inductive",
            "Math.Miu.Derivable": "inductive"
        }
        module = "Math.Logic.Miu"
        path = ROOT / "Math/Logic/Miu.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], "Math/Logic/Miu.lean")
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        for name, kind in expected.items():
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                self.assertEqual(node["kind"], kind)
                self.assertEqual(node["module"], module)
                if kind in {"theorem", "definition"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
        for constructor in ["ax", "I_", "II", "III", "IV"]:
            node = self.nodes["Math.Miu.Derivable." + constructor]
            self.assertEqual(node["kind"], "constructor")
            self.assertIn(node["name"], self.catalog["roots"])

    def test_miu_hierarchies_retain_rules_counts_and_complete_axiom_paths(self):
        expected = {
            "Math.Miu.derivable_iff": ["Math.Miu.Derivable", "Math.Miu.countI", "Math.Miu.countM",
                                       "Math.Miu.head_eq_M", "Math.Miu.body_of_mod_three"],
            "Math.Miu.mu_not_derivable": ["Math.Miu.countI_mod_three", "Math.Miu.Derivable"],
            "Math.Miu.theorem1": ["Math.Miu.Derivable.ax", "Math.Miu.Derivable.I_",
                                  "Math.Miu.Derivable.II", "Math.Miu.Derivable.III", "Math.Miu.Derivable.IV"],
            "Math.Miu.realize_body": ["Math.Miu.expansionCost", "Math.Miu.Derivable.III"],
        }
        graph = KnowledgeGraph(self.catalog)
        for name, required in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(required) <= reached, set(required) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for parent, child in zip(path, path[1:]):
                        self.assertIn(child, self.nodes[parent]["dependencies"])

    def test_miu_subjects_retain_logic_and_computation_boundaries(self):
        graph = KnowledgeGraph(self.catalog)
        self.assertEqual(self.catalog["subjects"]["miu_system"]["parent"], "formal_rewriting")
        self.assertEqual(self.catalog["subjects"]["formal_rewriting"]["parent"], "computation")
        for subject in ["miu_system", "formal_rewriting", "computation", "logic", "foundations", "mathematics"]:
            with self.subTest(subject=subject):
                self.assertIn("Math.Miu.derivable_iff", {node["name"] for node in
                              graph.search("Math.Miu.derivable_iff", subject=subject)})

    def test_miu_native_proof_translation_is_accepted_by_lean(self):
        from repository.metamath_build import open_snapshot as open_native
        from repository.miu import translate

        native = open_native(ROOT)
        try:
            result = translate(native, "metamath:miu.mm:theorem1")
            checked = native.declaration("metamath:miu.mm:theorem1")["checked"]["proof_digest"]
        finally:
            native.close()
        self.assertIn(checked, result)
        self.assertIn("example : Derivable [M, U, I, I, U]", result)
        self.assertEqual(result.count("  have step_"), 7)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Translation.lean"
            path.write_text(result)
            run(ROOT, [self.lake, "env", "lean", "-Ddebug.skipKernelTC=false", str(path)], capture=True)
            path.write_text(result.replace("example : Derivable [M, U, I, I, U]", "example : Derivable [M, U]"))
            with self.assertRaises(RepositoryError):
                run(ROOT, [self.lake, "env", "lean", str(path)], capture=True)

    def test_miu_translation_rejects_changed_sources_other_calculi_and_unresolved_symbols(self):
        from repository.metamath_audit import ProofError
        from repository.metamath_build import open_snapshot as open_native
        from repository.miu import lean_word, translate

        native = open_native(ROOT)
        try:
            with self.assertRaisesRegex(ProofError, "only for miu.mm"):
                translate(native, "metamath:set.mm:id")
            with self.assertRaisesRegex(ProofError, "proved statement"):
                translate(native, "metamath:miu.mm:ax")
            source = native.source
            with patch.object(native, "source", side_effect=lambda name, full=False: source(name, full) + b" "):
                with self.assertRaisesRegex(ProofError, "source differs"):
                    translate(native, "metamath:miu.mm:theorem1")
            declaration = native.declaration

            def changed_hypothesis(name):
                node = declaration(name)
                if name == "metamath:miu.mm:Ia":
                    node["expression"] = ["|-", "x", "U"]
                return node

            with patch.object(native, "declaration", side_effect=changed_hypothesis):
                with self.assertRaisesRegex(ProofError, "hypothesis differs"):
                    translate(native, "metamath:miu.mm:theorem1")
        finally:
            native.close()
        for tokens in [["x"], ["M", "I; sorry"], ["|-", "M"], [None], [[]]]:
            with self.subTest(tokens=tokens), self.assertRaises(ProofError):
                lean_word(tokens)

    def test_miu_translation_cli_preserves_the_checked_native_step_order(self):
        from repository.metamath import main as native_main

        output = io.StringIO()
        with redirect_stdout(output):
            result = native_main(["--root", str(ROOT), "translate-lean", "metamath:miu.mm:theorem1"])
        self.assertEqual(result, 0)
        source = output.getvalue()
        self.assertIn("import Math.Logic.Miu", source)
        labels = ["Derivable.ax", "Derivable.II", "Derivable.II", "Derivable.I_",
                  "Derivable.III", "Derivable.II", "Derivable.IV"]
        proof = [line.split(" := ", 1)[1].split(" ", 1)[0] for line in source.splitlines()
                 if line.startswith("  have step_")]
        self.assertEqual(proof, labels)

    def test_finite_averaging_results_retain_local_proofs_and_source(self):
        expected = {
            "Math.RepresentationTheory.averageMap_apply": "theorem",
            "Math.RepresentationTheory.averageMap_action": "theorem",
            "Math.RepresentationTheory.coinvariants_mk_averageMap": "theorem",
            "Math.RepresentationTheory.ker_averageMap": "theorem",
            "Math.RepresentationTheory.mem_invariants_iff_averageMap": "theorem",
            "Math.RepresentationTheory.range_averageMap": "theorem",
            "Math.RepresentationTheory.isCompl_invariants_coinvariantsKer": "theorem",
            "Math.RepresentationTheory.reynolds": "definition",
            "Math.RepresentationTheory.reynolds_coe": "theorem",
            "Math.RepresentationTheory.reynolds_invariant": "theorem",
            "Math.RepresentationTheory.reynolds_action": "theorem",
            "Math.RepresentationTheory.coinvariantsToInvariants": "definition",
            "Math.RepresentationTheory.invariantsToCoinvariants": "definition",
            "Math.RepresentationTheory.coinvariantsInvariantsEquiv": "definition",
            "Math.RepresentationTheory.coinvariantsInvariantsEquiv_mk": "theorem",
            "Math.RepresentationTheory.coinvariantsInvariantsEquiv_symm": "theorem",
            "Math.RepresentationTheory.averageMap_natural": "theorem",
            "Math.RepresentationTheory.mapInvariants": "definition",
            "Math.RepresentationTheory.mapInvariants_coe": "theorem",
            "Math.RepresentationTheory.mapInvariants_injective": "theorem",
            "Math.RepresentationTheory.coinvariantsInvariantsEquiv_natural": "theorem",
            "Math.RepresentationTheory.mapInvariants_surjective": "theorem",
            "Math.RepresentationTheory.mapInvariants_exact": "theorem",
            "Math.RepresentationTheory.invariantDifferenceEquiv": "definition",
            "Math.RepresentationTheory.invariantDifferenceEquiv_apply": "theorem"
        }
        module = "Math.Algebra.FiniteAveraging"
        path = ROOT / "Math/Algebra/FiniteAveraging.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name, kind in expected.items():
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                self.assertEqual(node["module"], module)
                self.assertEqual(node["kind"], kind)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ["representation_invariants", "finite_group_representations",
                                "representation_theory", "linear_algebra", "algebra", "mathematics"]:
                    self.assertIn(name, {item["name"] for item in graph.search(name, subject=subject)})

    def test_finite_averaging_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/FiniteAveragingStatements.lean"], capture=True)

    def test_group_representation_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/GroupRepresentationStatements.lean"], capture=True)

    def test_group_representation_registry_retains_complete_pinned_families(self):
        base = ROOT / ".lake/packages/mathlib"
        registered = self.policy["libraries"]["mathlib"]["modules"]
        for family, count in [("GroupTheory", 171), ("RepresentationTheory", 45)]:
            expected = {".".join(path.relative_to(base).with_suffix("").parts)
                        for path in (base / "Mathlib" / family).rglob("*.lean")}
            self.assertEqual(len(expected), count)
            self.assertEqual({name for name in registered if name.startswith("Mathlib." + family + ".")}, expected)
            for module in expected:
                with self.subTest(module=module):
                    self.assertIn(module, self.catalog["module_policy"])
                    self.assertIn(module, self.catalog["module_declarations_by_module"])
                    source = self.catalog["sources"][module]
                    self.assertEqual(source["revision"], self.policy["libraries"]["mathlib"]["revision"])
                    self.assertEqual(source["license"], "Apache-2.0")
                    self.assertEqual(source["sha256"], hashlib.sha256(
                        (base / (module.replace(".", "/") + ".lean")).read_bytes()).hexdigest())

    def test_group_representation_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "Group.nat_card_center_add_sum_card_noncenter_eq_card": "Mathlib.GroupTheory.ClassEquation",
            "Subgroup.card_subgroup_dvd_card": "Mathlib.GroupTheory.Coset.Card",
            "MulAction.orbitEquivQuotientStabilizer": "Mathlib.GroupTheory.GroupAction.Quotient",
            "Subgroup.exists_right_complement'_of_coprime": "Mathlib.GroupTheory.SchurZassenhaus",
            "subgroupIsFreeOfIsFree": "Mathlib.GroupTheory.FreeGroup.NielsenSchreier",
            "IsFreeGroup": "Mathlib.GroupTheory.FreeGroup.IsFreeGroup",
            "AddCommGroup.equiv_free_prod_directSum_zmod": "Mathlib.GroupTheory.FiniteAbelian.Basic",
            "AddCommGroup.equiv_directSum_zmod_of_finite": "Mathlib.GroupTheory.FiniteAbelian.Basic",
            "Group.IsNilpotent": "Mathlib.GroupTheory.Nilpotent",
            "IsNilpotent.to_isSolvable": "Mathlib.GroupTheory.Nilpotent",
            "Group.IsSolvable": "Mathlib.GroupTheory.Solvable",
            "derivedSeries_antitone": "Mathlib.GroupTheory.Solvable",
            "alternatingGroup.isSimpleGroup": "Mathlib.GroupTheory.SpecificGroups.Alternating.Simple",
            "alternatingGroup.isSolvable": "Mathlib.GroupTheory.SpecificGroups.Alternating.Simple",
            "Equiv.Perm.not_isSolvable_fin_5": "Mathlib.GroupTheory.Solvable",
            "Equiv.Perm.sign": "Mathlib.GroupTheory.Perm.Sign",
            "CoxeterSystem": "Mathlib.GroupTheory.Coxeter.Basic",
            "CoxeterSystem.simple_sq": "Mathlib.GroupTheory.Coxeter.Basic",
            "CoxeterSystem.length_inv": "Mathlib.GroupTheory.Coxeter.Length",
            "CoxeterSystem.length_mul_mod_two": "Mathlib.GroupTheory.Coxeter.Length",
            "GroupExtension": "Mathlib.GroupTheory.GroupExtension.Defs",
            "PresentedGroup": "Mathlib.GroupTheory.PresentedGroup",
            "Submonoid.LocalizationMap": "Mathlib.GroupTheory.MonoidLocalization.Basic",
            "Representation.invariants": "Mathlib.RepresentationTheory.Invariants",
            "Representation.Coinvariants": "Mathlib.RepresentationTheory.Coinvariants",
            "Representation.Coinvariants.ker": "Mathlib.RepresentationTheory.Coinvariants",
            "Representation.averageMap": "Mathlib.RepresentationTheory.Invariants",
            "Representation.isProj_averageMap": "Mathlib.RepresentationTheory.Invariants",
            "Representation.IntertwiningMap": "Mathlib.RepresentationTheory.Intertwining",
            "MonoidAlgebra.Submodule.exists_isCompl": "Mathlib.RepresentationTheory.Maschke",
            "Representation.IsSemisimpleRepresentation": "Mathlib.RepresentationTheory.Semisimple",
            "Representation.IsIrreducible": "Mathlib.RepresentationTheory.Irreducible",
            "Representation.character": "Mathlib.RepresentationTheory.Character",
            "Representation.char_orthonormal": "Mathlib.RepresentationTheory.Character",
            "Representation.card_inv_mul_sum_char_eq_finrank": "Mathlib.RepresentationTheory.Character",
            "Representation.card_inv_mul_sum_char_mul_char_eq_finrank": "Mathlib.RepresentationTheory.Character",
            "Representation.isIntegral_character": "Mathlib.RepresentationTheory.Character",
            "Representation.invariantsEquivIntertwiningMap": "Mathlib.RepresentationTheory.Invariants",
            "Rep.equivalenceModuleMonoidAlgebra": "Mathlib.RepresentationTheory.Rep.Iso",
            "groupCohomology.coindIso": "Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro",
            "groupHomology.indIso": "Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro",
            "groupCohomology.H0Iso": "Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree",
            "groupHomology.H0Iso": "Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree",
            "groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units": "Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90",
            "groupCohomology.exists_div_of_norm_eq_one": "Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90",
            "TannakaDuality.FiniteGroup.equiv": "Mathlib.RepresentationTheory.Tannaka",
            "IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed": "Mathlib.RepresentationTheory.AlgebraRepresentation.Basic",
            "ContRepresentation": "Mathlib.RepresentationTheory.Continuous.Basic",
            "continuousCohomology": "Mathlib.RepresentationTheory.Homological.ContCohomology.Basic",
            "Rep.ind": "Mathlib.RepresentationTheory.Induced",
            "Rep.coind": "Mathlib.RepresentationTheory.Coinduced",
            "Subrepresentation": "Mathlib.RepresentationTheory.Subrepresentation",
            "Rep.tateNorm": "Mathlib.RepresentationTheory.Homological.TateCohomology.Basic",
            "tateCohomology": "Mathlib.RepresentationTheory.Homological.TateCohomology.Basic"
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertIn(origin["revision"], origin["url"])

    def test_group_representation_hierarchies_retain_hypotheses_and_axiom_paths(self):
        expected = {
            "Math.RepresentationTheory.coinvariantsInvariantsEquiv": [
                "Representation.Coinvariants",
                "Math.RepresentationTheory.reynolds",
                "Math.RepresentationTheory.coinvariants_mk_averageMap",
                "Math.RepresentationTheory.reynolds_invariant",
                "Invertible",
                "Fintype"
            ],
            "Math.RepresentationTheory.ker_averageMap": [
                "Representation.Coinvariants.ker",
                "Submodule.span",
                "LinearMap.ker",
                "Representation.averageMap"
            ],
            "Math.RepresentationTheory.mapInvariants_exact": [
                "LinearMap.range",
                "LinearMap.ker",
                "Math.RepresentationTheory.mapInvariants",
                "Math.RepresentationTheory.averageMap_natural",
                "Math.RepresentationTheory.reynolds"
            ],
            "Math.RepresentationTheory.invariantDifferenceEquiv": [
                "Math.RepresentationTheory.isCompl_invariants_coinvariantsKer",
                "Submodule.prodEquivOfIsCompl",
                "Representation.invariants",
                "Representation.Coinvariants.ker"
            ],
            "AddCommGroup.equiv_directSum_zmod_of_finite": [
                "Finite",
                "Nat.Prime",
                "ZMod",
                "AddEquiv"
            ],
            "Subgroup.exists_right_complement'_of_coprime": [
                "Subgroup.Normal",
                "Nat.Coprime",
                "Subgroup.IsComplement'",
                "Subgroup.index"
            ],
            "subgroupIsFreeOfIsFree": [
                "IsFreeGroup",
                "Subgroup"
            ],
            "alternatingGroup.isSimpleGroup": [
                "Fintype",
                "DecidableEq",
                "IsSimpleGroup",
                "alternatingGroup"
            ],
            "TannakaDuality.FiniteGroup.equiv": [
                "IsDomain",
                "Finite",
                "TannakaDuality.FiniteGroup.forget",
                "CategoryTheory.Aut"
            ],
            "Representation.char_orthonormal": [
                "IsAlgClosed",
                "Invertible",
                "FiniteDimensional",
                "Representation.IsIrreducible",
                "Representation.Equiv"
            ],
            "groupCohomology.exists_div_of_norm_eq_one": [
                "IsGalois",
                "IsCyclic",
                "FiniteDimensional",
                "Algebra.norm",
                "Subgroup.zpowers"
            ],
            "groupCohomology.coindIso": [
                "Rep.coind",
                "groupCohomology",
                "Subgroup"
            ],
            "groupHomology.indIso": [
                "Rep.ind",
                "groupHomology",
                "DecidableEq"
            ],
            "continuousCohomology": [
                "TopRep",
                "TopologicalSpace"
            ],
            "IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed": [
                "IsSimpleModule",
                "IsAlgClosed",
                "FiniteDimensional",
                "Algebra",
                "Module.End"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_group_representation_subjects_retain_objects_and_parent_subjects(self):
        expected = {
            "group_actions": [
                "group_theory",
                "MulAction.orbitEquivQuotientStabilizer"
            ],
            "permutation_groups": [
                "group_theory",
                "alternatingGroup.isSimpleGroup"
            ],
            "finite_groups": [
                "group_theory",
                "Subgroup.exists_right_complement'_of_coprime"
            ],
            "abelian_groups": [
                "group_theory",
                "AddCommGroup.equiv_directSum_zmod_of_finite"
            ],
            "nilpotent_groups": [
                "group_theory",
                "Group.IsNilpotent"
            ],
            "solvable_groups": [
                "group_theory",
                "Group.IsSolvable"
            ],
            "free_groups": [
                "group_theory",
                "subgroupIsFreeOfIsFree"
            ],
            "group_presentations": [
                "group_theory",
                "PresentedGroup"
            ],
            "coxeter_groups": [
                "group_theory",
                "CoxeterSystem.length_inv"
            ],
            "group_extensions": [
                "group_theory",
                "GroupExtension"
            ],
            "monoid_localizations": [
                "algebra",
                "Submonoid.LocalizationMap"
            ],
            "representation_theory": [
                "algebra",
                "Math.RepresentationTheory.coinvariantsInvariantsEquiv"
            ],
            "representation_invariants": [
                "representation_theory",
                "Math.RepresentationTheory.ker_averageMap"
            ],
            "group_characters": [
                "representation_theory",
                "Representation.char_orthonormal"
            ],
            "finite_group_representations": [
                "representation_theory",
                "MonoidAlgebra.Submodule.exists_isCompl"
            ],
            "induced_representations": [
                "representation_theory",
                "Rep.ind"
            ],
            "topological_representations": [
                "representation_theory",
                "ContRepresentation"
            ],
            "group_homology": [
                "homological_algebra",
                "groupHomology.indIso"
            ],
            "group_cohomology": [
                "homological_algebra",
                "groupCohomology.coindIso"
            ],
            "continuous_group_cohomology": [
                "group_cohomology",
                "continuousCohomology"
            ],
            "tannaka_duality": [
                "representation_theory",
                "TannakaDuality.FiniteGroup.equiv"
            ],
            "algebra_representations": [
                "representation_theory",
                "IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                current = subject
                while current is not None:
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=current)})
                    current = self.catalog["subjects"][current]["parent"]

    def test_finite_etale_results_retain_local_proofs_and_source(self):
        expected = {
            "Math.Geometry.locallyQuasiFinite_of_unramified": "theorem",
            "Math.Geometry.finite_of_proper_etale": "theorem",
            "Math.Geometry.finite_iff_proper_of_etale": "theorem",
            "Math.Geometry.finite_of_proper_smooth_zero": "theorem",
            "Math.Geometry.FiniteEtale": "definition",
            "Math.Geometry.finiteEtale_iff_proper_smooth_zero": "theorem",
            "Math.Geometry.finiteEtale_id": "theorem",
            "Math.Geometry.finiteEtale_comp": "theorem",
            "Math.Geometry.finiteEtale_pullback_fst": "theorem",
            "Math.Geometry.finiteEtale_pullback_snd": "theorem",
            "Math.Geometry.finiteEtale_restrict": "theorem",
            "Math.Geometry.finiteEtale_of_comp": "theorem",
            "Math.Geometry.finiteEtale_comp_iff": "theorem",
            "Math.Geometry.finite_fibres_of_proper_etale": "theorem",
            "Math.Geometry.finite_preimage_of_proper_etale": "theorem",
            "Math.Geometry.discrete_fibres_of_etale": "theorem",
        }
        module = "Math.Geometry.FiniteEtale"
        path = ROOT / "Math/Geometry/FiniteEtale.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name, kind in expected.items():
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                self.assertEqual(node["module"], module)
                self.assertEqual(node["kind"], kind)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ["etale_geometry", "scheme_morphisms", "schemes", "algebraic_geometry", "geometry", "mathematics"]:
                    self.assertIn(name, {item["name"] for item in graph.search(name, subject=subject)})

    def test_finite_etale_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                   "tests/FiniteEtaleStatements.lean"], capture=True)

    def test_scheme_geometry_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/SchemeGeometryStatements.lean"], capture=True)

    def test_scheme_registry_retains_every_pinned_algebraic_geometry_module(self):
        base = ROOT / ".lake/packages/mathlib"
        expected = {".".join(path.relative_to(base).with_suffix("").parts)
                    for path in (base / "Mathlib/AlgebraicGeometry").rglob("*.lean")}
        self.assertEqual(len(expected), 140)
        registered = self.policy["libraries"]["mathlib"]["modules"]
        self.assertEqual({name for name in registered if name.startswith("Mathlib.AlgebraicGeometry.")}, expected)
        for module in expected:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                source = self.catalog["sources"][module]
                self.assertEqual(source["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertEqual(source["license"], "Apache-2.0")
                self.assertEqual(source["sha256"], hashlib.sha256(
                    (base / (module.replace(".", "/") + ".lean")).read_bytes()).hexdigest())

    def test_scheme_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "AlgebraicGeometry.Scheme": "Scheme",
            "AlgebraicGeometry.Scheme.Spec": "Scheme",
            "AlgebraicGeometry.AffineScheme": "AffineScheme",
            "AlgebraicGeometry.IsAffine": "AffineScheme",
            "AlgebraicGeometry.AffineScheme.equivCommRingCat": "AffineScheme",
            "AlgebraicGeometry.Scheme.affineCover": "Cover.Open",
            "AlgebraicGeometry.Etale": "Morphisms.Etale",
            "AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero": "Morphisms.Etale",
            "AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified": "Morphisms.Etale",
            "AlgebraicGeometry.IsProper": "Morphisms.Proper",
            "AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom": "Morphisms.Proper",
            "AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite": "ZariskisMainTheorem",
            "AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono": "ZariskisMainTheorem",
            "AlgebraicGeometry.IsProper.eq_valuativeCriterion": "ValuativeCriterion",
            "AlgebraicGeometry.Scheme.Hom.fiber": "Fiber",
            "AlgebraicGeometry.Scheme.Hom.fiberHomeo": "Fiber",
            "AlgebraicGeometry.IsNoetherian": "Noetherian",
            "AlgebraicGeometry.isNoetherian_Spec": "Noetherian",
            "AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian": "Noetherian",
            "AlgebraicGeometry.Scheme.Hom.normalization": "Normalization",
            "AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization": "Normalization",
            "AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen": "FunctionField",
            "AlgebraicGeometry.Scheme.RationalMap": "Birational.RationalMap",
            "AlgebraicGeometry.Scheme.RationalMap.equivFunctionField": "Birational.RationalMap",
            "AlgebraicGeometry.Proj.valuativeCriterion_existence": "ProjectiveSpectrum.Proper",
            "AlgebraicGeometry.Scheme.etalePrecoverage": "Sites.Etale",
            "AlgebraicGeometry.Scheme.smallEtaleTopology": "Sites.Etale",
            "AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology": "Sites.Etale",
            "AlgebraicGeometry.Scheme.Modules": "Modules.Sheaf",
            "AlgebraicGeometry.Scheme.IdealSheafData": "IdealSheaf.Basic",
            "AlgebraicGeometry.Scheme.IdealSheafData.subscheme": "IdealSheaf.Subscheme",
            "AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral": "Group.Abelian",
            "WeierstrassCurve.Affine.Point": "EllipticCurve.Affine.Point",
            "WeierstrassCurve.Affine.Point.toClass_injective": "EllipticCurve.Affine.Point",
            "WeierstrassCurve.LFunction": "EllipticCurve.LFunction",
            "WeierstrassCurve.LSeries": "EllipticCurve.LFunction",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                module = "Mathlib.AlgebraicGeometry." + suffix
                self.assertEqual(node["module"], module)
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertIn(origin["revision"], origin["url"])

    def test_scheme_hierarchies_retain_hypotheses_and_axiom_paths(self):
        expected = {
            "Math.Geometry.finite_of_proper_etale": [
                "AlgebraicGeometry.IsProper", "AlgebraicGeometry.Etale", "AlgebraicGeometry.IsFinite",
                "Math.Geometry.locallyQuasiFinite_of_unramified",
                "AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite"],
            "Math.Geometry.finiteEtale_iff_proper_smooth_zero": [
                "Math.Geometry.FiniteEtale", "AlgebraicGeometry.SmoothOfRelativeDimension",
                "AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero"],
            "Math.Geometry.finiteEtale_of_comp": [
                "AlgebraicGeometry.IsSeparated", "AlgebraicGeometry.LocallyOfFiniteType",
                "AlgebraicGeometry.FormallyUnramified", "AlgebraicGeometry.Etale.of_comp"],
            "Math.Geometry.finite_preimage_of_proper_etale": [
                "AlgebraicGeometry.Scheme.Hom.finite_preimage", "Set.Finite"],
            "Math.Geometry.discrete_fibres_of_etale": ["IsDiscrete", "AlgebraicGeometry.Etale"],
            "AlgebraicGeometry.IsProper.eq_valuativeCriterion": [
                "AlgebraicGeometry.ValuativeCriterion", "AlgebraicGeometry.QuasiCompact",
                "AlgebraicGeometry.QuasiSeparated", "AlgebraicGeometry.LocallyOfFiniteType"],
            "AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen": [
                "AlgebraicGeometry.IsIntegral", "AlgebraicGeometry.IsAffineOpen", "IsFractionRing"],
        }
        graph = KnowledgeGraph(self.catalog)
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_scheme_subjects_retain_objects_and_parent_subjects(self):
        expected = {
            "schemes": ("algebraic_geometry", "AlgebraicGeometry.Scheme"),
            "affine_schemes": ("schemes", "AlgebraicGeometry.AffineScheme.equivCommRingCat"),
            "scheme_morphisms": ("schemes", "Math.Geometry.finite_of_proper_etale"),
            "scheme_covers": ("schemes", "AlgebraicGeometry.Scheme.affineCover"),
            "scheme_topologies": ("schemes", "AlgebraicGeometry.Scheme.smallEtaleTopology"),
            "etale_geometry": ("schemes", "Math.Geometry.finiteEtale_iff_proper_smooth_zero"),
            "projective_geometry": ("algebraic_geometry", "AlgebraicGeometry.Proj.valuativeCriterion_existence"),
            "elliptic_curves": ("algebraic_geometry", "WeierstrassCurve.Affine.Point.toClass_injective"),
            "birational_geometry": ("algebraic_geometry", "AlgebraicGeometry.Scheme.RationalMap.equivFunctionField"),
            "scheme_modules": ("schemes", "AlgebraicGeometry.Scheme.Modules"),
            "group_schemes": ("schemes", "AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral"),
            "scheme_fibres": ("schemes", "AlgebraicGeometry.Scheme.Hom.fiberHomeo"),
            "scheme_ideals": ("schemes", "AlgebraicGeometry.Scheme.IdealSheafData.subscheme"),
        }
        graph = KnowledgeGraph(self.catalog)
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                current = subject
                while current is not None:
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=current)})
                    current = self.catalog["subjects"][current]["parent"]

    def test_prime_progression_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/PrimeProgressionStatements.lean"], capture=True)

    def test_analytic_number_theory_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/AnalyticNumberTheoryStatements.lean"], capture=True)

    def test_modular_form_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ModularFormStatements.lean"], capture=True)

    def test_analytic_number_theory_registry_retains_every_pinned_module(self):
        base = ROOT / ".lake/packages/mathlib"
        areas = {'NumberTheory/LSeries': 23, 'NumberTheory/ArithmeticFunction': 8, 'NumberTheory/DirichletCharacter': 4, 'NumberTheory/EulerProduct': 3, 'NumberTheory/ModularForms': 39}
        registered = self.policy["libraries"]["mathlib"]["modules"]
        total = set()
        for area, count in areas.items():
            paths = (base / "Mathlib" / area).rglob("*.lean")
            expected = {".".join(path.relative_to(base).with_suffix("").parts) for path in paths}
            self.assertEqual(len(expected), count)
            prefix = "Mathlib." + area.replace("/", ".") + "."
            self.assertEqual({name for name in registered if name.startswith(prefix)}, expected)
            total |= expected
        total.update({"Mathlib.NumberTheory.ZetaValues", "Mathlib.NumberTheory.Harmonic.ZetaAsymp"})
        self.assertEqual(len(total), 79)
        for module in total:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                self.assertIn(module, self.catalog["sources"])

    def test_analytic_number_theory_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "ModularForm": "Mathlib.NumberTheory.ModularForms.Basic",
            "CuspForm": "Mathlib.NumberTheory.ModularForms.Basic",
            "ArithmeticFunction.vonMangoldt": "Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt",
            "ArithmeticFunction": "Mathlib.NumberTheory.ArithmeticFunction.Defs",
            "LSeries": "Mathlib.NumberTheory.LSeries.Basic",
            "DirichletCharacter.LFunction": "Mathlib.NumberTheory.LSeries.DirichletContinuation",
            "DirichletCharacter": "Mathlib.NumberTheory.DirichletCharacter.Basic",
            "riemannZeta": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq": "Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing",
            "UpperHalfPlane.qExpansion": "Mathlib.NumberTheory.ModularForms.QExpansion",
            "zeta_eq_tsum_one_div_nat_add_one_cpow": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "completedRiemannZeta": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "ArithmeticFunction.zeta": "Mathlib.NumberTheory.ArithmeticFunction.Zeta",
            "ArithmeticFunction.moebius": "Mathlib.NumberTheory.ArithmeticFunction.Moebius",
            "ArithmeticFunction.moebius_mul_coe_zeta": "Mathlib.NumberTheory.ArithmeticFunction.Moebius",
            "ArithmeticFunction.IsMultiplicative": "Mathlib.NumberTheory.ArithmeticFunction.Defs",
            "ModularForm.discriminant": "Mathlib.NumberTheory.ModularForms.Discriminant",
            "ModularForm.eta": "Mathlib.NumberTheory.ModularForms.DedekindEta",
            "ModularForm.discriminant_ne_zero": "Mathlib.NumberTheory.ModularForms.Discriminant",
            "ModularForm.eta_ne_zero": "Mathlib.NumberTheory.ModularForms.DedekindEta",
            "CuspForm.rank_eq_one_of_weight_eq_twelve": "Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula",
            "CuspForm.discriminantEquiv": "Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula",
            "CuspForm.discriminant": "Mathlib.NumberTheory.ModularForms.Discriminant",
            "hasSum_zeta_two": "Mathlib.NumberTheory.ZetaValues",
            "ModularForm.Λ": "Mathlib.NumberTheory.ModularForms.LFunction",
            "ModularForm.L": "Mathlib.NumberTheory.ModularForms.LFunction",
            "UpperHalfPlane.petersson": "Mathlib.NumberTheory.ModularForms.Petersson",
            "riemannZeta_neg_two_mul_nat_add_one": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "DirichletCharacter.LFunction_eq_LSeries": "Mathlib.NumberTheory.LSeries.DirichletContinuation",
            "riemannZeta_residue_one": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "Nat.infinite_setOfPred_prime_and_modEq": "Mathlib.NumberTheory.LSeries.PrimesInAP",
            "ArithmeticFunction.vonMangoldt.residueClass": "Mathlib.NumberTheory.LSeries.PrimesInAP",
            "ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div": "Mathlib.NumberTheory.LSeries.PrimesInAP",
            "LSeries.abscissaOfAbsConv": "Mathlib.NumberTheory.LSeries.Convergence",
            "DirichletCharacter.LFunction_ne_zero_of_one_le_re": "Mathlib.NumberTheory.LSeries.Nonvanishing",
            "DirichletCharacter.LSeries_eulerProduct_hasProd": "Mathlib.NumberTheory.EulerProduct.DirichletLSeries",
            "DirichletCharacter.differentiable_LFunction": "Mathlib.NumberTheory.LSeries.DirichletContinuation",
            "DirichletCharacter.completedLFunction": "Mathlib.NumberTheory.LSeries.DirichletContinuation",
            "DirichletCharacter.IsPrimitive.completedLFunction_one_sub": "Mathlib.NumberTheory.LSeries.DirichletContinuation",
            "jacobiTheta": "Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable",
            "riemannZetaZeros": "Mathlib.NumberTheory.LSeries.ZetaZeros",
            "completedRiemannZeta₀": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "ModularForm.sturm_bound_levelOne": "Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula",
            "ModularForm.dimension_level_one": "Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula",
            "LSeries.eq_of_LSeries_eventually_eq": "Mathlib.NumberTheory.LSeries.Injectivity",
            "IsCompact.inter_riemannZetaZeros_finite": "Mathlib.NumberTheory.LSeries.ZetaZeros",
            "isDiscrete_riemannZetaZeros": "Mathlib.NumberTheory.LSeries.ZetaZeros",
            "riemannZeta_ne_zero_of_one_le_re": "Mathlib.NumberTheory.LSeries.Nonvanishing",
            "DirichletCharacter.LFunction_apply_one_ne_zero": "Mathlib.NumberTheory.LSeries.Nonvanishing",
            "CuspForm.differentiable_Λ": "Mathlib.NumberTheory.ModularForms.LFunction",
            "CuspForm.differentiable_L": "Mathlib.NumberTheory.ModularForms.LFunction",
            "ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq": "Mathlib.NumberTheory.ArithmeticFunction.Moebius",
            "riemannZeta_zero": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "riemannZeta_one_sub": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "hasSum_zeta_four": "Mathlib.NumberTheory.ZetaValues",
            "riemannZeta_eulerProduct_hasProd": "Mathlib.NumberTheory.EulerProduct.DirichletLSeries",
            "logDeriv_riemannZeta_one_sub": "Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv",
            "jacobiTheta_S_smul": "Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable",
            "differentiable_completedZeta₀": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "RiemannHypothesis": "Mathlib.NumberTheory.LSeries.RiemannZeta",
            "ModularForm.E₆": "Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic",
            "ModularForm.E₄": "Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic",
            "Math.NumberTheory.prime_eq_gcd_of_not_coprime": "Math.NumberTheory.PrimeProgressions",
            "Math.NumberTheory.finite_primes_modEq_of_not_coprime": "Math.NumberTheory.PrimeProgressions",
            "Math.NumberTheory.infinite_primes_modEq_iff": "Math.NumberTheory.PrimeProgressions",
            "Math.NumberTheory.infinite_primes_modEq_above_avoiding_iff": "Math.NumberTheory.PrimeProgressions",
            "Math.NumberTheory.exists_prime_modEq_above_avoiding": "Math.NumberTheory.PrimeProgressions",
            "Math.NumberTheory.exists_finset_primes_modEq_card": "Math.NumberTheory.PrimeProgressions",
            "Math.NumberTheory.forall_finset_exists_prime_modEq_iff": "Math.NumberTheory.PrimeProgressions",
            "Math.NumberTheory.modularForm_eq_zero_iff_coeffs": "Math.NumberTheory.SturmFinite",
            "Math.NumberTheory.modularForm_eq_iff_coeffs": "Math.NumberTheory.SturmFinite",
            "Math.NumberTheory.sturmCoefficients_injective": "Math.NumberTheory.SturmFinite",
            "Math.NumberTheory.sturmCoefficients": "Math.NumberTheory.SturmFinite"
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                if module.startswith("Mathlib."):
                    self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                    self.assertEqual(origin["license"], "Apache-2.0")
                    self.assertIn(origin["revision"], origin["url"])
                else:
                    self.assertEqual(origin["package"], "math")

    def test_analytic_number_theory_hierarchies_retain_models_hypotheses_and_axiom_paths(self):
        expected = {
            "Math.NumberTheory.prime_eq_gcd_of_not_coprime": [
                "Nat.gcd",
                "Nat.Prime",
                "Nat.ModEq",
                "Nat.ModEq.dvd_iff",
                "Nat.Prime.eq_one_or_self_of_dvd"
            ],
            "Math.NumberTheory.infinite_primes_modEq_iff": [
                "Nat.infinite_setOfPred_prime_and_modEq",
                "Math.NumberTheory.finite_primes_modEq_of_not_coprime",
                "Nat.Coprime"
            ],
            "Math.NumberTheory.exists_finset_primes_modEq_card": [
                "Set.Infinite.exists_subset_card_eq",
                "Math.NumberTheory.infinite_primes_modEq_above_avoiding_iff"
            ],
            "Math.NumberTheory.modularForm_eq_iff_coeffs": [
                "Math.NumberTheory.modularForm_eq_zero_iff_coeffs",
                "ModularForm.sturm_bound_levelOne",
                "UpperHalfPlane.qExpansion",
                "PowerSeries.nat_le_order",
                "CuspForm.discriminantEquiv"
            ],
            "Math.NumberTheory.sturmCoefficients_injective": [
                "Math.NumberTheory.modularForm_eq_iff_coeffs",
                "Math.NumberTheory.sturmCoefficients"
            ],
            "Nat.infinite_setOfPred_prime_and_modEq": [
                "ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div",
                "DirichletCharacter.LFunction_ne_zero_of_one_le_re",
                "DirichletCharacter.LFunction_eq_LSeries"
            ],
            "riemannZeta_eulerProduct_hasProd": [
                "riemannZeta",
                "HasProd"
            ],
            "DirichletCharacter.LFunction_ne_zero_of_one_le_re": [
                "DirichletCharacter.LFunction",
                "DirichletCharacter.LFunction_eq_LSeries",
                "DirichletCharacter.LSeries_ne_zero_of_one_lt_re"
            ],
            "riemannZeta_one_sub": [
                "HurwitzZeta.hurwitzZetaEven",
                "Complex.Gamma",
                "Complex.cos"
            ],
            "ModularForm.dimension_level_one": [
                "CuspForm.discriminantEquiv",
                "ModularForm.levelOne_weight_two_rank_zero"
            ],
            "ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq": [
                "CuspForm.exists_smul_discriminant_of_weight_eq_twelve",
                "ModularForm.E₄",
                "ModularForm.E₆",
                "ModularForm.discriminant_qExpansion_coeff_one"
            ],
            "CuspForm.differentiable_L": [
                "ModularForm.L",
                "CuspForm.differentiable_Λ"
            ],
            "jacobiTheta_S_smul": [
                "jacobiTheta₂_functional_equation",
                "jacobiTheta",
                "Complex.cpow"
            ],
            "ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq": [
                "ArithmeticFunction.moebius_mul_coe_zeta",
                "ArithmeticFunction.coe_zeta_mul_moebius",
                "Nat.divisors"
            ],
            "riemannZeta_residue_one": [
                "Filter.Tendsto",
                "riemannZeta"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_analytic_number_theory_subjects_retain_results_and_parent_subjects(self):
        expected = {
            "analytic_number_theory": [
                "number_theory",
                "Math.NumberTheory.infinite_primes_modEq_iff"
            ],
            "dirichlet_series": [
                "analytic_number_theory",
                "LSeries.eq_of_LSeries_eventually_eq"
            ],
            "zeta_functions": [
                "dirichlet_series",
                "riemannZeta_residue_one"
            ],
            "arithmetic_functions": [
                "number_theory",
                "ArithmeticFunction.moebius_mul_coe_zeta"
            ],
            "dirichlet_characters": [
                "analytic_number_theory",
                "DirichletCharacter.LFunction_ne_zero_of_one_le_re"
            ],
            "primes_in_progressions": [
                "analytic_number_theory",
                "Math.NumberTheory.exists_finset_primes_modEq_card"
            ],
            "modular_forms": [
                "number_theory",
                "ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq"
            ],
            "eisenstein_series": [
                "modular_forms",
                "ModularForm.E₄"
            ],
            "theta_functions": [
                "modular_forms",
                "jacobiTheta_S_smul"
            ],
            "modular_l_functions": [
                "modular_forms",
                "CuspForm.differentiable_L"
            ],
            "modular_identity_certificates": [
                "modular_forms",
                "Math.NumberTheory.sturmCoefficients_injective"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                current = subject
                while current is not None:
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=current)})
                    current = self.catalog["subjects"][current]["parent"]

    def test_analytic_number_theory_references_retain_pinned_records(self):
        expected = {
            "ModularForm.discriminant_ne_zero": "diamondshurman2005"
        }
        snapshot = open_snapshot(ROOT)
        for name, key in expected.items():
            with self.subTest(name=name):
                citations = snapshot.citations(name)
                self.assertIn(key, {entry["key"] for entry in citations["module_citations"]})

    def test_riemann_hypothesis_is_an_unproved_formulation(self):
        node = self.nodes["RiemannHypothesis"]
        self.assertEqual(node["kind"], "definition")
        self.assertEqual(node["statement"], "Prop")
        self.assertIsInstance(node["value"], int)
        self.assertIn("RiemannHypothesis", self.catalog["roots"])
        self.assertNotIn("RiemannHypothesis", self.policy["axioms"])

    def test_conditional_l2_results_retain_local_proofs_and_source(self):
        expected = {
            "Math.Probability.aestronglyMeasurable_l2Predictor": "theorem",
            "Math.Probability.l2Predictor_eq_self_iff": "theorem",
            "Math.Probability.l2Predictor_idempotent": "theorem",
            "Math.Probability.inner_residual_l2Predictor_eq_zero": "theorem",
            "Math.Probability.l2_prediction_error_sq": "theorem",
            "Math.Probability.l2_norm_sq_decomposition": "theorem",
            "Math.Probability.l2_prediction_error_minimal": "theorem",
            "Math.Probability.l2_prediction_error_eq_iff": "theorem",
            "Math.Probability.dist_l2Predictor_le": "theorem",
            "Math.Probability.l2Predictor_larger_fixes_smaller": "theorem",
            "Math.Probability.l2Predictor_tower": "theorem",
            "Math.Probability.l2_prediction_information_gap": "theorem",
            "Math.Probability.l2_prediction_error_antitone": "theorem",
            "Math.Probability.l2Predictor": "definition"
        }
        module = "Math.Probability.ConditionalL2"
        path = ROOT / "Math/Probability/ConditionalL2.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name, kind in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                node = self.nodes[name]
                self.assertEqual(node["kind"], kind)
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ("conditional_expectation", "measure_theory", "probability", "hilbert_spaces", "functional_analysis", "analysis", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_conditional_l2_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ConditionalL2Statements.lean"], capture=True)

    def test_measure_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/MeasureStatements.lean"], capture=True)

    def test_measure_registry_retains_every_pinned_module(self):
        base = ROOT / ".lake/packages/mathlib"
        areas = {"MeasureTheory/Measure": 94, "MeasureTheory/Integral": 64, "MeasureTheory/MeasurableSpace": 14,
                 "MeasureTheory/OuterMeasure": 9, "MeasureTheory/Function/ConditionalExpectation": 11}
        registered = self.policy["libraries"]["mathlib"]["modules"]
        total = set()
        for area, count in areas.items():
            paths = (base / "Mathlib" / area).rglob("*.lean")
            expected = {".".join(path.relative_to(base).with_suffix("").parts) for path in paths}
            self.assertEqual(len(expected), count)
            prefix = "Mathlib." + area.replace("/", ".") + "."
            self.assertEqual({name for name in registered if name.startswith(prefix)}, expected)
            total |= expected
        total.add("Mathlib.MeasureTheory.Function.ConditionalLExpectation")
        self.assertEqual(len(total), 193)
        for module in total:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                self.assertIn(module, self.catalog["sources"])

    def test_measure_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "MeasurableSpace": "Mathlib.MeasureTheory.MeasurableSpace.Defs",
            "MeasurableSet": "Mathlib.MeasureTheory.MeasurableSpace.Defs",
            "Measurable": "Mathlib.MeasureTheory.MeasurableSpace.Defs",
            "MeasureTheory.Measure": "Mathlib.MeasureTheory.Measure.MeasureSpaceDef",
            "MeasureTheory.IsFiniteMeasure": "Mathlib.MeasureTheory.Measure.Typeclasses.Finite",
            "MeasureTheory.SigmaFinite": "Mathlib.MeasureTheory.Measure.Typeclasses.SFinite",
            "MeasureTheory.IsProbabilityMeasure": "Mathlib.MeasureTheory.Measure.Typeclasses.Probability",
            "MeasureTheory.Measure.prod": "Mathlib.MeasureTheory.Measure.Prod",
            "MeasureTheory.Measure.withDensity": "Mathlib.MeasureTheory.Measure.WithDensity",
            "MeasureTheory.Measure.HaveLebesgueDecomposition": "Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue",
            "MeasureTheory.Measure.rnDeriv": "Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue",
            "MeasureTheory.Measure.singularPart": "Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue",
            "MeasureTheory.Measure.haveLebesgueDecomposition_add": "Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue",
            "MeasureTheory.Measure.withDensity_rnDeriv_eq": "Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym",
            "MeasureTheory.lintegral_rnDeriv_mul": "Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym",
            "MeasureTheory.integral_rnDeriv_smul": "Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym",
            "MeasureTheory.Measure.rnDeriv_mul_rnDeriv": "Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym",
            "MeasureTheory.lintegral_iSup": "Mathlib.MeasureTheory.Integral.Lebesgue.Add",
            "MeasureTheory.lintegral_liminf_le'": "Mathlib.MeasureTheory.Integral.Lebesgue.Add",
            "MeasureTheory.tendsto_integral_of_dominated_convergence": "Mathlib.MeasureTheory.Integral.DominatedConvergence",
            "MeasureTheory.lintegral_prod": "Mathlib.MeasureTheory.Measure.Prod",
            "MeasureTheory.integral_prod": "Mathlib.MeasureTheory.Integral.Prod",
            "MeasureTheory.integral_integral_swap": "Mathlib.MeasureTheory.Integral.Prod",
            "MeasureTheory.condExpL2": "Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2",
            "MeasureTheory.lpMeas": "Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable",
            "MeasureTheory.condExp": "Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic",
            "MeasureTheory.setIntegral_condExp": "Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic",
            "MeasureTheory.condExp_condExp_of_le": "Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic",
            "MeasureTheory.condExp_mul_of_aestronglyMeasurable_left": "Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut",
            "MeasureTheory.toReal_condLExp": "Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner",
            "MeasureTheory.condLExp": "Mathlib.MeasureTheory.Function.ConditionalLExpectation",
            "MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le": "Mathlib.MeasureTheory.Integral.DivergenceTheorem",
            "MeasureTheory.Measure.haarMeasure": "Mathlib.MeasureTheory.Measure.Haar.Basic",
            "MeasureTheory.Measure.haarMeasure_unique": "Mathlib.MeasureTheory.Measure.Haar.Basic",
            "RealRMK.rieszMeasure": "Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real",
            "RealRMK.integral_rieszMeasure": "Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real",
            "intervalIntegral.integral_eq_sub_of_hasDerivAt": "Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus",
            "intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt": "Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts",
            "Math.Probability.aestronglyMeasurable_l2Predictor": "Math.Probability.ConditionalL2",
            "Math.Probability.l2Predictor_eq_self_iff": "Math.Probability.ConditionalL2",
            "Math.Probability.l2Predictor_idempotent": "Math.Probability.ConditionalL2",
            "Math.Probability.inner_residual_l2Predictor_eq_zero": "Math.Probability.ConditionalL2",
            "Math.Probability.l2_prediction_error_sq": "Math.Probability.ConditionalL2",
            "Math.Probability.l2_norm_sq_decomposition": "Math.Probability.ConditionalL2",
            "Math.Probability.l2_prediction_error_minimal": "Math.Probability.ConditionalL2",
            "Math.Probability.l2_prediction_error_eq_iff": "Math.Probability.ConditionalL2",
            "Math.Probability.dist_l2Predictor_le": "Math.Probability.ConditionalL2",
            "Math.Probability.l2Predictor_larger_fixes_smaller": "Math.Probability.ConditionalL2",
            "Math.Probability.l2Predictor_tower": "Math.Probability.ConditionalL2",
            "Math.Probability.l2_prediction_information_gap": "Math.Probability.ConditionalL2",
            "Math.Probability.l2_prediction_error_antitone": "Math.Probability.ConditionalL2",
            "Math.Probability.l2Predictor": "Math.Probability.ConditionalL2",
            "MeasureTheory.integral": "Mathlib.MeasureTheory.Integral.Bochner.Basic",
            "MeasureTheory.integral_add": "Mathlib.MeasureTheory.Integral.Bochner.Basic",
            "MeasureTheory.ProbabilityMeasure": "Mathlib.MeasureTheory.Measure.ProbabilityMeasure"
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                if module.startswith("Mathlib."):
                    self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                    self.assertEqual(origin["license"], "Apache-2.0")
                    self.assertIn(origin["revision"], origin["url"])
                else:
                    self.assertEqual(origin["package"], "math")

    def test_measure_hierarchies_retain_models_hypotheses_and_axiom_paths(self):
        expected = {
            "Math.Probability.l2_prediction_error_minimal": [
                "Math.Probability.l2_prediction_error_sq",
                "Math.Probability.inner_residual_l2Predictor_eq_zero",
                "MeasureTheory.lpMeas",
                "MeasureTheory.condExpL2",
                "Submodule.starProjection_inner_eq_zero"
            ],
            "Math.Probability.l2_prediction_error_eq_iff": [
                "Math.Probability.l2_prediction_error_sq",
                "MeasureTheory.Lp",
                "Submodule.starProjection"
            ],
            "Math.Probability.l2Predictor_tower": [
                "Submodule.starProjection_comp_starProjection_of_le",
                "MeasureTheory.lpMeas",
                "MeasureTheory.condExpL2"
            ],
            "Math.Probability.l2_prediction_information_gap": [
                "Math.Probability.l2_prediction_error_sq",
                "MeasureTheory.AEStronglyMeasurable"
            ],
            "Math.Probability.dist_l2Predictor_le": [
                "Submodule.lipschitzWith_starProjection",
                "Math.Probability.l2Predictor"
            ],
            "MeasureTheory.Measure.withDensity_rnDeriv_eq": [
                "MeasureTheory.Measure.rnDeriv",
                "MeasureTheory.Measure.withDensity",
                "MeasureTheory.Measure.HaveLebesgueDecomposition"
            ],
            "MeasureTheory.tendsto_integral_of_dominated_convergence": [
                "MeasureTheory.Integrable",
                "MeasureTheory.AEStronglyMeasurable",
                "Filter.Tendsto"
            ],
            "MeasureTheory.integral_prod": [
                "MeasureTheory.Integrable",
                "MeasureTheory.Measure.prod",
                "MeasureTheory.integral"
            ],
            "MeasureTheory.lintegral_prod": [
                "MeasureTheory.Measure.prod",
                "MeasureTheory.lintegral",
                "AEMeasurable"
            ],
            "MeasureTheory.condExp_condExp_of_le": [
                "MeasureTheory.condExp",
                "MeasureTheory.Measure.trim",
                "MeasureTheory.SigmaFinite"
            ],
            "RealRMK.integral_rieszMeasure": [
                "RealRMK.rieszMeasure",
                "MeasureTheory.integral",
                "CompactlySupportedContinuousMap"
            ],
            "MeasureTheory.Measure.haarMeasure_unique": [
                "MeasureTheory.Measure.haarMeasure",
                "MeasureTheory.SigmaFinite"
            ],
            "MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le": [
                "HasFDerivAt",
                "ContinuousOn",
                "MeasureTheory.IntegrableOn",
                "intervalIntegral"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_measure_subjects_retain_results_and_parent_subjects(self):
        expected = {
            "integration": [
                "measure_theory",
                "MeasureTheory.integral_prod"
            ],
            "lebesgue_integration": [
                "integration",
                "MeasureTheory.lintegral_iSup"
            ],
            "bochner_integration": [
                "integration",
                "MeasureTheory.integral_add"
            ],
            "interval_integration": [
                "integration",
                "intervalIntegral.integral_eq_sub_of_hasDerivAt"
            ],
            "measure_decomposition": [
                "measure_theory",
                "MeasureTheory.Measure.withDensity_rnDeriv_eq"
            ],
            "haar_measure": [
                "measure_theory",
                "MeasureTheory.Measure.haarMeasure_unique"
            ],
            "conditional_expectation": [
                "measure_theory",
                "Math.Probability.l2_prediction_error_minimal"
            ],
            "probability_measures": [
                "probability",
                "MeasureTheory.ProbabilityMeasure"
            ],
            "line_and_surface_integrals": [
                "integration",
                "MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                current = subject
                while current is not None:
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=current)})
                    current = self.catalog["subjects"][current]["parent"]

    def test_measure_references_retain_pinned_records(self):
        expected = {
            "RealRMK.integral_rieszMeasure": ("Rud87", "rudin1987"),
            "MeasureTheory.Measure.haarMeasure_unique": ("halmos1950measure", "halmos1950measure")
        }
        snapshot = open_snapshot(ROOT)
        for name, (original, canonical) in expected.items():
            with self.subTest(name=name):
                citations = snapshot.citations(name)
                entry = next(item for item in citations["module_citations"] if item["citation_key"] == original)
                self.assertEqual(entry["key"], canonical)
                self.assertIn("mathlib:" + original, snapshot.summary()["bibliography_keys"])
                self.assertEqual(entry["raw"], self.catalog["bibliographies"]["mathlib"]["entries"][canonical]["raw"])
                if original != canonical:
                    self.assertEqual(entry["alias"], original)
                    self.assertEqual(self.policy["libraries"]["mathlib"]["citation_aliases"][original], canonical)

    def test_convex_geometry_coverage_retains_every_pinned_module(self):
        base = ROOT / ".lake/packages/mathlib"
        areas = {"Geometry/Euclidean": 44, "Geometry/Convex": 24, "Analysis/Convex": 66, "Geometry/Polygon": 1}
        registered = self.policy["libraries"]["mathlib"]["modules"]
        for area, count in areas.items():
            paths = (base / "Mathlib" / area).rglob("*.lean")
            expected = {".".join(path.relative_to(base).with_suffix("").parts) for path in paths}
            self.assertEqual(len(expected), count)
            prefix = "Mathlib." + area.replace("/", ".") + "."
            self.assertEqual({name for name in registered if name.startswith(prefix)}, expected)
            for module in expected:
                with self.subTest(module=module):
                    self.assertIn(module, self.catalog["module_policy"])
                    self.assertIn(module, self.catalog["module_declarations_by_module"])
                    self.assertIn(module, self.catalog["sources"])

    def test_finite_convex_geometry_retains_local_proofs_and_source(self):
        names = [
            "Math.ConvexGeometry.exists_finset_card_le_finrank_succ",
            "Math.ConvexGeometry.convexHull_eq_union_card_le_finrank_succ",
            "Math.ConvexGeometry.exists_positive_weights_card_le_finrank_succ",
            "Math.ConvexGeometry.radon_partition_of_finrank_lt_card",
            "Math.ConvexGeometry.radon_partition_finrank_add_two"
        ]
        module = "Math.Geometry.ConvexFinite"
        path = ROOT / "Math/Geometry/ConvexFinite.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name in names:
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                node = self.nodes[name]
                self.assertEqual(node["kind"], "theorem")
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ("convex_geometry", "convex_analysis", "euclidean_geometry", "geometry", "analysis", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_convex_geometry_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ConvexGeometryStatements.lean"], capture=True)

    def test_euclidean_geometry_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/EuclideanGeometryStatements.lean"], capture=True)

    def test_convex_geometry_objects_and_results_retain_terms_and_sources(self):
        expected = {
            "Convexity.StdSimplex": "Mathlib.Geometry.Convex.ConvexSpace.Defs",
            "Convexity.ConvexSpace": "Mathlib.Geometry.Convex.ConvexSpace.Defs",
            "Convexity.IsAffineMap": "Mathlib.Geometry.Convex.ConvexSpace.Defs",
            "Convexity.IsConvexSet": "Mathlib.Geometry.Convex.Set",
            "Convexity.convexHull": "Mathlib.Geometry.Convex.Hull",
            "Convex": "Mathlib.Analysis.Convex.Basic",
            "convexHull": "Mathlib.Analysis.Convex.Hull",
            "ConvexOn": "Mathlib.Analysis.Convex.Function",
            "StrictConvexOn": "Mathlib.Analysis.Convex.Function",
            "Set.extremePoints": "Mathlib.Analysis.Convex.Extreme",
            "ConvexCone": "Mathlib.Geometry.Convex.Cone.Basic",
            "PointedCone": "Mathlib.Geometry.Convex.Cone.Pointed",
            "ProperCone": "Mathlib.Analysis.Convex.Cone.Basic",
            "ProperCone.innerDual": "Mathlib.Analysis.Convex.Cone.InnerDual",
            "ProperCone.innerDual_innerDual": "Mathlib.Analysis.Convex.Cone.InnerDual",
            "convexHull_eq_union": "Mathlib.Analysis.Convex.Caratheodory",
            "eq_pos_convex_span_of_mem_convexHull": "Mathlib.Analysis.Convex.Caratheodory",
            "Convex.radon_partition": "Mathlib.Analysis.Convex.Radon",
            "Convex.helly_theorem": "Mathlib.Analysis.Convex.Radon",
            "Convex.helly_theorem_compact": "Mathlib.Analysis.Convex.Radon",
            "IsCompact.extremePoints_nonempty": "Mathlib.Analysis.Convex.KreinMilman",
            "closure_convexHull_extremePoints": "Mathlib.Analysis.Convex.KreinMilman",
            "ConvexOn.map_sum_le": "Mathlib.Analysis.Convex.Jensen",
            "StrictConvexOn.map_sum_eq_iff_of_pos": "Mathlib.Analysis.Convex.Jensen",
            "doublyStochastic_eq_convexHull_permMatrix": "Mathlib.Analysis.Convex.Birkhoff",
            "extremePoints_doublyStochastic": "Mathlib.Analysis.Convex.Birkhoff",
            "exists_eq_sum_perm_of_mem_doublyStochastic": "Mathlib.Analysis.Convex.Birkhoff",
            "exists_convex_convex_compl_subset": "Mathlib.Analysis.Convex.StoneSeparation",
            "Convex.contractibleSpace": "Mathlib.Analysis.Convex.Contractible",
            "EuclideanGeometry.Sphere": "Mathlib.Geometry.Euclidean.Sphere.Basic",
            "EuclideanGeometry.Cospherical": "Mathlib.Geometry.Euclidean.Sphere.Basic",
            "EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle": "Mathlib.Geometry.Euclidean.Triangle",
            "EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist": "Mathlib.Geometry.Euclidean.Triangle",
            "EuclideanGeometry.angle_add_angle_add_angle_eq_pi": "Mathlib.Geometry.Euclidean.Triangle",
            "EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq": "Mathlib.Geometry.Euclidean.Triangle",
            "EuclideanGeometry.dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_of_angle_eq_pi_div_two": "Mathlib.Geometry.Euclidean.BritishFlag",
            "EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist": "Mathlib.Geometry.Euclidean.Inversion.Basic",
            "EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical": "Mathlib.Geometry.Euclidean.Sphere.Ptolemy",
            "EuclideanGeometry.inversion": "Mathlib.Geometry.Euclidean.Inversion.Basic",
            "EuclideanGeometry.inversion_inversion": "Mathlib.Geometry.Euclidean.Inversion.Basic",
            "EuclideanGeometry.dist_inversion_inversion": "Mathlib.Geometry.Euclidean.Inversion.Basic",
            "Affine.Simplex.ninePointCircle": "Mathlib.Geometry.Euclidean.NinePointCircle",
            "Affine.Simplex.eulerPoint": "Mathlib.Geometry.Euclidean.NinePointCircle",
            "Affine.Simplex.eulerPoint_mem_ninePointCircle": "Mathlib.Geometry.Euclidean.NinePointCircle",
            "Affine.Triangle.altitudeFoot_mem_ninePointCircle": "Mathlib.Geometry.Euclidean.NinePointCircle",
            "Affine.Simplex.volume_eq_euclideanHausdorffMeasure_real_closedInterior": "Mathlib.Geometry.Euclidean.Volume.MeasureSimplex",
            "Math.ConvexGeometry.exists_finset_card_le_finrank_succ": "Math.Geometry.ConvexFinite",
            "Math.ConvexGeometry.convexHull_eq_union_card_le_finrank_succ": "Math.Geometry.ConvexFinite",
            "Math.ConvexGeometry.exists_positive_weights_card_le_finrank_succ": "Math.Geometry.ConvexFinite",
            "Math.ConvexGeometry.radon_partition_of_finrank_lt_card": "Math.Geometry.ConvexFinite",
            "Math.ConvexGeometry.radon_partition_finrank_add_two": "Math.Geometry.ConvexFinite"
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                if module.startswith("Mathlib."):
                    self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                    self.assertEqual(origin["license"], "Apache-2.0")
                    self.assertIn(origin["revision"], origin["url"])
                else:
                    self.assertEqual(origin["package"], "math")

    def test_convex_geometry_hierarchies_retain_models_hypotheses_and_axiom_paths(self):
        expected = {
            "Math.ConvexGeometry.exists_finset_card_le_finrank_succ": [
                "Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull",
                "AffineIndependent.card_le_finrank_succ",
                "convexHull"
            ],
            "Math.ConvexGeometry.exists_positive_weights_card_le_finrank_succ": [
                "eq_pos_convex_span_of_mem_convexHull",
                "AffineIndependent.card_le_finrank_succ",
                "convexHull"
            ],
            "Math.ConvexGeometry.radon_partition_finrank_add_two": [
                "Math.ConvexGeometry.radon_partition_of_finrank_lt_card",
                "Convex.radon_partition",
                "AffineIndependent.card_le_finrank_succ"
            ],
            "closure_convexHull_extremePoints": [
                "Set.extremePoints",
                "convexHull",
                "IsCompact.extremePoints_nonempty",
                "geometric_hahn_banach_closed_point"
            ],
            "convexHull_eq_union": [
                "AffineIndependent",
                "convexHull",
                "Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull"
            ],
            "Convex.helly_theorem": [
                "Convex.radon_partition",
                "Module.finrank",
                "Convex",
                "convexHull"
            ],
            "ConvexOn.map_sum_le": [
                "ConvexOn",
                "Finset.centerMass",
                "Convex"
            ],
            "doublyStochastic_eq_convexHull_permMatrix": [
                "doublyStochastic",
                "convexHull",
                "exists_eq_sum_perm_of_mem_doublyStochastic"
            ],
            "EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle": [
                "EuclideanGeometry.angle",
                "Real.cos",
                "InnerProductSpace"
            ],
            "EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical": [
                "EuclideanGeometry.Cospherical",
                "EuclideanGeometry.angle"
            ],
            "Affine.Triangle.altitudeFoot_mem_ninePointCircle": [
                "Affine.Simplex.ninePointCircle",
                "Affine.Simplex.eulerPoint",
                "Affine.Simplex.circumcenter"
            ],
            "EuclideanGeometry.inversion_inversion": [
                "EuclideanGeometry.inversion",
                "EuclideanGeometry.dist_inversion_center"
            ],
            "exists_convex_convex_compl_subset": [
                "Convex",
                "zorn_subset_nonempty"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_convex_geometry_subjects_retain_results_and_parents(self):
        expected = {
            "euclidean_geometry": [
                "geometry",
                "EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist"
            ],
            "triangle_geometry": [
                "euclidean_geometry",
                "EuclideanGeometry.angle_add_angle_add_angle_eq_pi"
            ],
            "circles_and_spheres": [
                "euclidean_geometry",
                "Affine.Triangle.altitudeFoot_mem_ninePointCircle"
            ],
            "convex_geometry": [
                "geometry",
                "convexHull_eq_union"
            ],
            "convex_analysis": [
                "analysis",
                "closure_convexHull_extremePoints"
            ],
            "convex_cones": [
                "convex_geometry",
                "ProperCone.innerDual_innerDual"
            ],
            "convex_functions": [
                "convex_analysis",
                "ConvexOn.map_sum_le"
            ]
        }
        graph = KnowledgeGraph(self.catalog)
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for ancestor in (subject, parent, "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=ancestor)})

    def test_convex_geometry_references_retain_pinned_records(self):
        snapshot = open_snapshot(ROOT)
        references = snapshot.citations("closure_convexHull_extremePoints")
        self.assertIn("simon2011", {entry["key"] for entry in references["module_citations"]})

    def test_harnack_sharpness_retains_local_proofs_and_source(self):
        expected = {
            "Math.ComplexAnalysis.harnackExtremal": "definition",
            "Math.ComplexAnalysis.upperHarnackConstants": "definition",
            "Math.ComplexAnalysis.lowerHarnackConstants": "definition",
            "Math.ComplexAnalysis.harmonic_harnackExtremal": "theorem",
            "Math.ComplexAnalysis.nonneg_harnackExtremal": "theorem",
            "Math.ComplexAnalysis.harnackExtremal_center": "theorem",
            "Math.ComplexAnalysis.harnackExtremal_add_real": "theorem",
            "Math.ComplexAnalysis.harnackExtremal_sub_real": "theorem",
            "Math.ComplexAnalysis.upperHarnackConstants_eq_Ici": "theorem",
            "Math.ComplexAnalysis.lowerHarnackConstants_eq_Iic": "theorem",
        }
        module = "Math.Analysis.HarnackSharpness"
        path = ROOT / "Math/Analysis/HarnackSharpness.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name, kind in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                node = self.nodes[name]
                self.assertEqual(node["kind"], kind)
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ("harmonic_functions", "complex_analysis", "partial_differential_equations",
                                "analysis", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_harnack_sharpness_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/HarnackSharpnessStatements.lean"], capture=True)

    def test_harnack_sharpness_hierarchies_retain_extremizers_and_axiom_paths(self):
        expected = {
            "Math.ComplexAnalysis.upperHarnackConstants_eq_Ici": {
                "Math.ComplexAnalysis.upperHarnackConstants",
                "Math.ComplexAnalysis.harnackExtremal",
                "Math.ComplexAnalysis.harmonic_harnackExtremal",
                "Math.ComplexAnalysis.nonneg_harnackExtremal",
                "Math.ComplexAnalysis.harnackExtremal_center",
                "Math.ComplexAnalysis.harnackExtremal_add_real",
                "Math.ComplexAnalysis.harnack_on_closedBall",
                "poissonKernel",
                "InnerProductSpace.HarmonicOnNhd",
            },
            "Math.ComplexAnalysis.lowerHarnackConstants_eq_Iic": {
                "Math.ComplexAnalysis.lowerHarnackConstants",
                "Math.ComplexAnalysis.harnackExtremal",
                "Math.ComplexAnalysis.harmonic_harnackExtremal",
                "Math.ComplexAnalysis.nonneg_harnackExtremal",
                "Math.ComplexAnalysis.harnackExtremal_center",
                "Math.ComplexAnalysis.harnackExtremal_sub_real",
                "Math.ComplexAnalysis.harnack_on_closedBall",
                "poissonKernel",
                "InnerProductSpace.HarmonicOnNhd",
            },
        }
        graph = KnowledgeGraph(self.catalog)
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_compact_complex_rigidity_retains_local_proofs_and_source(self):
        names = [
            "Math.ComplexGeometry.range_subsingleton",
            "Math.ComplexGeometry.mfderiv_eq_zero",
            "Math.ComplexGeometry.injective_iff_subsingleton",
            "Math.ComplexGeometry.not_injective",
            "Math.ComplexGeometry.not_surjective",
            "Math.ComplexGeometry.not_injective_mfderiv",
            "Math.ComplexGeometry.not_isImmersionAt",
            "Math.ComplexGeometry.not_isImmersion"
        ]
        module = "Math.Geometry.CompactComplex"
        path = ROOT / "Math/Geometry/CompactComplex.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name in names:
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                self.assertEqual(node["kind"], "theorem")
                self.assertIsInstance(node["value"], int)
                self.assertTrue(node["proof"])
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ("smooth_manifolds", "differential_geometry", "geometry",
                                "complex_analysis", "holomorphic_functions", "analysis", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_manifold_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ManifoldStatements.lean"], capture=True)

    def test_manifold_coverage_retains_every_pinned_module(self):
        base = ROOT / ".lake/packages/mathlib"
        paths = (base / "Mathlib/Geometry/Manifold").rglob("*.lean")
        expected = {".".join(path.relative_to(base).with_suffix("").parts) for path in paths}
        registered = self.policy["libraries"]["mathlib"]["modules"]
        self.assertEqual({name for name in registered if name.startswith("Mathlib.Geometry.Manifold.")}, expected)
        self.assertEqual(len(expected), 79)
        for module in expected:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                self.assertIn(module, self.catalog["sources"])

    def test_manifold_objects_and_results_retain_terms_and_sources(self):
        expected = {
            "ChartedSpace": "Mathlib.Geometry.Manifold.ChartedSpace",
            "StructureGroupoid": "Mathlib.Geometry.Manifold.StructureGroupoid",
            "HasGroupoid": "Mathlib.Geometry.Manifold.HasGroupoid",
            "ModelWithCorners": "Mathlib.Geometry.Manifold.IsManifold.Basic",
            "IsManifold": "Mathlib.Geometry.Manifold.IsManifold.Basic",
            "TangentSpace": "Mathlib.Geometry.Manifold.IsManifold.Basic",
            "TangentBundle": "Mathlib.Geometry.Manifold.IsManifold.Basic",
            "ContMDiff": "Mathlib.Geometry.Manifold.ContMDiff.Defs",
            "ContMDiffAt": "Mathlib.Geometry.Manifold.ContMDiff.Defs",
            "MDifferentiable": "Mathlib.Geometry.Manifold.MFDeriv.Defs",
            "MDifferentiableAt": "Mathlib.Geometry.Manifold.MFDeriv.Defs",
            "mfderiv": "Mathlib.Geometry.Manifold.MFDeriv.Defs",
            "tangentMap": "Mathlib.Geometry.Manifold.MFDeriv.Defs",
            "mfderiv_comp": "Mathlib.Geometry.Manifold.MFDeriv.Basic",
            "mfderiv_comp_apply": "Mathlib.Geometry.Manifold.MFDeriv.Basic",
            "tangentMap_comp": "Mathlib.Geometry.Manifold.MFDeriv.Basic",
            "Diffeomorph": "Mathlib.Geometry.Manifold.Diffeomorph",
            "Diffeomorph.isInvertible_mfderiv": "Mathlib.Geometry.Manifold.LocalDiffeomorph",
            "IsLocalDiffeomorphAt": "Mathlib.Geometry.Manifold.LocalDiffeomorph",
            "IsLocalDiffeomorphAt.isInvertible_mfderiv": "Mathlib.Geometry.Manifold.LocalDiffeomorph",
            "Manifold.IsImmersionAt": "Mathlib.Geometry.Manifold.Immersion",
            "Manifold.IsSubmersionAt": "Mathlib.Geometry.Manifold.Submersion",
            "SmoothBumpFunction": "Mathlib.Geometry.Manifold.BumpFunction",
            "SmoothPartitionOfUnity": "Mathlib.Geometry.Manifold.PartitionOfUnity",
            "SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source": "Mathlib.Geometry.Manifold.PartitionOfUnity",
            "Continuous.exists_contMDiff_approx": "Mathlib.Geometry.Manifold.SmoothApprox",
            "Continuous.exists_contMDiff_approx_and_eqOn": "Mathlib.Geometry.Manifold.SmoothApprox",
            "exists_contMDiff_zero_iff_one_iff_of_isClosed": "Mathlib.Geometry.Manifold.PartitionOfUnity",
            "exists_embedding_euclidean_of_compact": "Mathlib.Geometry.Manifold.WhitneyEmbedding",
            "GroupLieAlgebra": "Mathlib.Geometry.Manifold.GroupLieAlgebra",
            "mulInvariantVectorField": "Mathlib.Geometry.Manifold.GroupLieAlgebra",
            "instLieAlgebraGroupLieAlgebra": "Mathlib.Geometry.Manifold.GroupLieAlgebra",
            "IsMIntegralCurve": "Mathlib.Geometry.Manifold.IntegralCurve.Basic",
            "IsMIntegralCurveAt": "Mathlib.Geometry.Manifold.IntegralCurve.Basic",
            "exists_isMIntegralCurveAt_of_contMDiffAt": "Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique",
            "isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless": "Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique",
            "IsMIntegralCurve.periodic_of_eq": "Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique",
            "IsMIntegralCurve.periodic_xor_injective": "Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique",
            "Bundle.RiemannianBundle": "Mathlib.Topology.VectorBundle.Riemannian",
            "IsContMDiffRiemannianBundle": "Mathlib.Geometry.Manifold.VectorBundle.Riemannian",
            "CovariantDerivative": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic",
            "CovariantDerivative.IsLeviCivitaConnection": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita",
            "CovariantDerivative.IsLeviCivitaConnection.apply_eq": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita",
            "CovariantDerivative.IsLeviCivitaConnection.uniqueness": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita",
            "CovariantDerivative.leviCivitaConnection": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita",
            "CovariantDerivative.isMetricCompatible_leviCivitaConnection": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita",
            "CovariantDerivative.torsion_leviCivitaConnection_eq_zero": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita",
            "CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection": "Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita",
            "VectorField.mlieBracket": "Mathlib.Geometry.Manifold.VectorField.LieBracket",
            "Manifold.pathELength": "Mathlib.Geometry.Manifold.Riemannian.PathELength",
            "Manifold.riemannianEDist": "Mathlib.Geometry.Manifold.Riemannian.PathELength",
            "Manifold.riemannianEDist_triangle": "Mathlib.Geometry.Manifold.Riemannian.PathELength",
            "Manifold.riemannianEDist_comm": "Mathlib.Geometry.Manifold.Riemannian.PathELength",
            "Manifold.riemannianEDist_le_pathELength": "Mathlib.Geometry.Manifold.Riemannian.PathELength",
            "MDifferentiable.exists_eq_const_of_compactSpace": "Mathlib.Geometry.Manifold.Complex",
            "ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere": "Mathlib.Geometry.Manifold.PoincareConjecture"
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if module in self.policy["libraries"]["mathlib"]["modules"]:
                    self.assertIn(name, self.catalog["roots"])
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertEqual(origin["license"], "Apache-2.0")
                self.assertIn(origin["revision"], origin["url"])

    def test_manifold_hierarchies_retain_models_hypotheses_and_axiom_paths(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "mfderiv_comp": [
                "mfderiv",
                "MDifferentiableAt",
                "ContinuousLinearMap",
                "ModelWithCorners",
                "ChartedSpace"
            ],
            "Diffeomorph.isInvertible_mfderiv": [
                "Diffeomorph",
                "mfderiv",
                "ContinuousLinearEquiv",
                "IsLocalDiffeomorphAt"
            ],
            "exists_embedding_euclidean_of_compact": [
                "CompactSpace",
                "IsManifold",
                "SmoothBumpCovering",
                "EuclideanSpace",
                "Topology.IsClosedEmbedding",
                "mfderiv"
            ],
            "Continuous.exists_contMDiff_approx": [
                "ContMDiff",
                "Continuous",
                "SmoothPartitionOfUnity",
                "Dist.dist"
            ],
            "exists_contMDiff_zero_iff_one_iff_of_isClosed": [
                "ContMDiff",
                "IsClosed",
                "SmoothPartitionOfUnity",
                "Set.Icc"
            ],
            "IsMIntegralCurve.periodic_xor_injective": [
                "IsMIntegralCurve",
                "ContMDiff",
                "BoundarylessManifold",
                "Function.Periodic",
                "Function.Injective"
            ],
            "exists_isMIntegralCurveAt_of_contMDiffAt": [
                "IsMIntegralCurveAt",
                "ModelWithCorners",
                "CompleteSpace",
                "IsPicardLindelof"
            ],
            "CovariantDerivative.IsLeviCivitaConnection.apply_eq": [
                "CovariantDerivative",
                "VectorField.mlieBracket",
                "Inner.inner",
                "mfderiv"
            ],
            "CovariantDerivative.IsLeviCivitaConnection.uniqueness": [
                "CovariantDerivative.IsLeviCivitaConnection",
                "MDifferentiableAt",
                "TangentSpace"
            ],
            "CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection": [
                "CovariantDerivative.leviCivitaConnection",
                "CovariantDerivative.IsLeviCivitaConnection",
                "IsContMDiffRiemannianBundle",
                "FiniteDimensional"
            ],
            "Manifold.riemannianEDist_triangle": [
                "Manifold.riemannianEDist",
                "Manifold.pathELength",
                "ENNReal",
                "ContMDiff"
            ],
            "MDifferentiable.exists_eq_const_of_compactSpace": [
                "MDifferentiable",
                "CompactSpace",
                "PreconnectedSpace",
                "Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax"
            ],
            "instLieAlgebraGroupLieAlgebra": [
                "GroupLieAlgebra",
                "VectorField.mlieBracket",
                "LieAlgebra",
                "LieGroup",
                "CompleteSpace"
            ],
            "Math.ComplexGeometry.mfderiv_eq_zero": [
                "MDifferentiable.exists_eq_const_of_compactSpace",
                "mfderiv_const",
                "CompactSpace",
                "PreconnectedSpace",
                "ModelWithCorners"
            ],
            "Math.ComplexGeometry.not_isImmersionAt": [
                "Math.ComplexGeometry.mfderiv_eq_zero",
                "Math.ComplexGeometry.not_injective_mfderiv",
                "Manifold.IsImmersionAt",
                "Nontrivial",
                "MDifferentiable"
            ],
            "Math.ComplexGeometry.not_isImmersion": [
                "Math.ComplexGeometry.not_injective_mfderiv",
                "Manifold.IsImmersion",
                "Nonempty",
                "ModelWithCorners"
            ]
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_manifold_subjects_retain_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "differential_geometry": ("geometry", "CovariantDerivative.leviCivitaConnection"),
            "smooth_manifolds": ("differential_geometry", "exists_embedding_euclidean_of_compact"),
            "manifold_calculus": ("differential_geometry", "mfderiv_comp"),
            "vector_bundles": ("differential_geometry", "CovariantDerivative"),
            "riemannian_geometry": ("differential_geometry", "CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection"),
            "lie_groups": ("differential_geometry", "instLieAlgebraGroupLieAlgebra"),
            "manifold_dynamics": ("dynamical_systems", "IsMIntegralCurve.periodic_xor_injective"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "differential_geometry", "geometry", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_manifold_references_retain_their_pinned_records(self):
        snapshot = open_snapshot(ROOT)
        for name in ("exists_isMIntegralCurveAt_of_contMDiffAt", "IsMIntegralCurve.periodic_xor_injective"):
            with self.subTest(name=name):
                references = snapshot.citations(name)
                self.assertIn("lee2012", {entry["key"] for entry in references["module_citations"]})

    def test_poincare_module_records_a_conjecture_formulation(self):
        module = "Mathlib.Geometry.Manifold.PoincareConjecture"
        node = self.nodes["ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere"]
        self.assertEqual(node["module"], module)
        self.assertEqual(node["kind"], "definition")
        self.assertIn("Prop", node["statement"])
        self.assertIn("formulation", self.catalog["module_policy"][module]["title"].lower())

    def test_harmonic_maximum_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/HarmonicMaximumStatements.lean"], capture=True)

    def test_harnack_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/HarnackStatements.lean"], capture=True)

    def test_harmonic_principles_retain_local_proofs_and_source(self):
        expected = {
            "Math.Analysis.Harnack": [
                "Math.ComplexAnalysis.harnack_lower",
                "Math.ComplexAnalysis.harnack_upper",
                "Math.ComplexAnalysis.harnack_lower_on_ball",
                "Math.ComplexAnalysis.harnack_upper_on_ball",
                "Math.ComplexAnalysis.harnack_on_closedBall",
                "Math.ComplexAnalysis.eq_zero_on_ball_of_harmonic_nonneg",
                "Math.ComplexAnalysis.eq_zero_iff_center_of_harmonic_nonneg",
                "Math.ComplexAnalysis.pos_on_ball_of_harmonic_nonneg",
                "Math.ComplexAnalysis.eq_zero_on_preconnected_of_harmonic_nonneg",
                "Math.ComplexAnalysis.eq_on_preconnected_of_harmonic_min",
                "Math.ComplexAnalysis.eq_on_preconnected_of_harmonic_max",
                "Math.ComplexAnalysis.eq_of_entire_harmonic_nonneg",
                "Math.ComplexAnalysis.eq_of_entire_harmonic_bddBelow",
                "Math.ComplexAnalysis.eq_of_entire_harmonic_bddAbove"
            ],
            "Math.Analysis.HarmonicMaximum": [
                "Math.ComplexAnalysis.poissonKernel_nonneg_on_sphere",
                "Math.ComplexAnalysis.circleAverage_poissonKernel_eq_one",
                "Math.ComplexAnalysis.harmonic_norm_le_boundary_bound",
                "Math.ComplexAnalysis.harmonic_dist_le_boundary_bound"
            ]
        }
        for module, names in expected.items():
            path = ROOT / (module.replace(".", "/") + ".lean")
            origin = self.catalog["sources"][module]
            self.assertEqual(origin["package"], "math")
            self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
            self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
            for name in names:
                with self.subTest(name=name):
                    self.assertIn(name, self.catalog["roots"])
                    self.assertIn(name, self.catalog["module_declarations_by_module"][module])
                    node = self.nodes[name]
                    self.assertEqual(node["module"], module)
                    self.assertEqual(node["kind"], "theorem")
                    self.assertIsInstance(node["value"], int)
                    self.assertTrue(node["proof"])
                    self.assertGreater(node["source"]["line"], 0)
                    self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))

    def test_harnack_hierarchies_retain_hypotheses_and_axiom_paths(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "Math.ComplexAnalysis.harnack_lower": {
                "Math.ComplexAnalysis.harmonic_poisson_formula",
                "InnerProductSpace.HarmonicContOnCl",
                "poissonKernel",
                "Real.circleAverage_mono",
                "le_re_herglotzRieszKernel",
            },
            "Math.ComplexAnalysis.harnack_upper": {
                "Math.ComplexAnalysis.harmonic_poisson_formula",
                "re_herglotzRieszKernel_le",
                "Metric.sphere",
            },
            "Math.ComplexAnalysis.harnack_lower_on_ball": {
                "Math.ComplexAnalysis.harnack_lower",
                "InnerProductSpace.HarmonicOnNhd",
                "Metric.ball",
                "le_of_tendsto",
            },
            "Math.ComplexAnalysis.harnack_on_closedBall": {
                "Math.ComplexAnalysis.harnack_lower_on_ball",
                "Math.ComplexAnalysis.harnack_upper_on_ball",
                "Metric.closedBall",
            },
            "Math.ComplexAnalysis.eq_zero_on_preconnected_of_harmonic_nonneg": {
                "Math.ComplexAnalysis.harnack_upper_on_ball",
                "IsPreconnected",
                "IsOpen",
                "IsClopen",
                "ContinuousOn",
            },
            "Math.ComplexAnalysis.eq_on_preconnected_of_harmonic_min": {
                "Math.ComplexAnalysis.eq_zero_on_preconnected_of_harmonic_nonneg",
                "InnerProductSpace.HarmonicOnNhd",
                "IsPreconnected",
            },
            "Math.ComplexAnalysis.eq_of_entire_harmonic_nonneg": {
                "Math.ComplexAnalysis.harnack_upper_on_ball",
                "Filter.Tendsto.const_div_atTop",
                "InnerProductSpace.HarmonicOnNhd",
            },
            "Math.ComplexAnalysis.eq_of_entire_harmonic_bddBelow": {
                "Math.ComplexAnalysis.eq_of_entire_harmonic_nonneg",
                "BddBelow",
                "Set.range",
            },
            "Math.ComplexAnalysis.eq_of_entire_harmonic_bddAbove": {
                "Math.ComplexAnalysis.eq_of_entire_harmonic_nonneg",
                "BddAbove",
                "Set.range",
            },
            "Math.ComplexAnalysis.circleAverage_poissonKernel_eq_one": {
                "Math.ComplexAnalysis.harmonic_poisson_formula",
                "Real.circleAverage",
                "poissonKernel",
            },
            "Math.ComplexAnalysis.harmonic_norm_le_boundary_bound": {
                "Math.ComplexAnalysis.poissonKernel_nonneg_on_sphere",
                "Math.ComplexAnalysis.circleAverage_poissonKernel_eq_one",
                "Real.norm_circleAverage_le_circleAverage_norm",
                "InnerProductSpace.HarmonicContOnCl",
                "CompleteSpace",
                "NormedSpace",
                "Metric.closedBall",
            },
            "Math.ComplexAnalysis.harmonic_dist_le_boundary_bound": {
                "Math.ComplexAnalysis.harmonic_norm_le_boundary_bound",
                "InnerProductSpace.HarmonicContOnCl.sub",
                "dist_eq_norm",
            },
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_harnack_principles_belong_to_harmonic_functions_and_pde(self):
        graph = KnowledgeGraph(self.catalog)
        module = "Math.Analysis.Harnack"
        names = {name for name in self.catalog["roots"]
                 if self.nodes[name]["module"] in {module, "Math.Analysis.HarmonicMaximum"}}
        for subject in ("harmonic_functions", "complex_analysis", "partial_differential_equations",
                        "analysis", "mathematics"):
            with self.subTest(subject=subject):
                actual = {node["name"] for node in graph.search("Math.ComplexAnalysis", subject=subject)}
                self.assertTrue(names <= actual, names - actual)

    def test_complex_analysis_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/ComplexAnalysisStatements.lean"], capture=True)

    def test_complex_analysis_covers_every_module_in_its_pinned_directories(self):
        base = ROOT / ".lake/packages/mathlib"
        directories = ("Mathlib/Analysis/Complex", "Mathlib/Analysis/Analytic", "Mathlib/Analysis/Meromorphic")
        expected = {".".join(path.relative_to(base).with_suffix("").parts)
                    for directory in directories for path in (base / directory).rglob("*.lean")}
        prefixes = tuple(directory.replace("/", ".") + "." for directory in directories)
        registered = self.policy["libraries"]["mathlib"]["modules"]
        self.assertEqual({name for name in registered if name.startswith(prefixes)}, expected)
        self.assertEqual(len(expected), 102)
        for module in expected:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                self.assertIn(module, self.catalog["sources"])

    def test_complex_analysis_objects_retain_terms_and_pinned_sources(self):
        expected = {'AnalyticAt': 'Mathlib.Analysis.Analytic.Basic',
         'AnalyticOnNhd': 'Mathlib.Analysis.Analytic.Basic',
         'HasFPowerSeriesAt': 'Mathlib.Analysis.Analytic.Basic',
         'HasFPowerSeriesOnBall': 'Mathlib.Analysis.Analytic.Basic',
         'AnalyticAt.eventually_eq_zero_or_eventually_ne_zero': 'Mathlib.Analysis.Analytic.IsolatedZeros',
         'AnalyticAt.frequently_eq_iff_eventually_eq': 'Mathlib.Analysis.Analytic.IsolatedZeros',
         'AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq': 'Mathlib.Analysis.Analytic.IsolatedZeros',
         'AnalyticOnNhd.eq_of_frequently_eq': 'Mathlib.Analysis.Analytic.IsolatedZeros',
         'AnalyticAt.analyticOrderAt_deriv_add_one': 'Mathlib.Analysis.Analytic.Order',
         'FormalMultilinearSeries.radius_eq_liminf': 'Mathlib.Analysis.Analytic.RadiusLiminf',
         'FormalMultilinearSeries.radius_inv_eq_limsup': 'Mathlib.Analysis.Analytic.RadiusLiminf',
         'FormalMultilinearSeries.leftInv': 'Mathlib.Analysis.Analytic.Inverse',
         'FormalMultilinearSeries.leftInv_eq_rightInv': 'Mathlib.Analysis.Analytic.Inverse',
         'DiffContOnCl.circleIntegral_eq_zero': 'Mathlib.Analysis.Complex.CauchyIntegral',
         'DiffContOnCl.circleIntegral_sub_inv_smul': 'Mathlib.Analysis.Complex.CauchyIntegral',
         'DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul': 'Mathlib.Analysis.Complex.CauchyIntegral',
         'DifferentiableOn.circleIntegral_sub_inv_smul': 'Mathlib.Analysis.Complex.CauchyIntegral',
         'DifferentiableOn.analyticOnNhd': 'Mathlib.Analysis.Complex.CauchyIntegral',
         'Differentiable.deriv': 'Mathlib.Analysis.Complex.CauchyIntegral',
         'Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le': 'Mathlib.Analysis.Complex.Liouville',
         'Complex.norm_deriv_le_of_forall_mem_sphere_norm_le': 'Mathlib.Analysis.Complex.Liouville',
         'Complex.hasSum_taylorSeries_on_ball': 'Mathlib.Analysis.Complex.TaylorSeries',
         'Complex.hasSum_taylorSeries_of_entire': 'Mathlib.Analysis.Complex.TaylorSeries',
         'Complex.taylorSeries_eq_of_entire': 'Mathlib.Analysis.Complex.TaylorSeries',
         'Complex.norm_le_norm_of_mapsTo_ball': 'Mathlib.Analysis.Complex.Schwarz',
         'Complex.norm_deriv_le_one_of_mapsTo_ball': 'Mathlib.Analysis.Complex.Schwarz',
         'Complex.norm_deriv_le_div_of_mapsTo_ball': 'Mathlib.Analysis.Complex.Schwarz',
         'Complex.norm_le_of_forall_mem_frontier_norm_le': 'Mathlib.Analysis.Complex.AbsMax',
         'Complex.eqOn_closure_of_eqOn_frontier': 'Mathlib.Analysis.Complex.AbsMax',
         'AnalyticOnNhd.is_constant_or_isOpenMap': 'Mathlib.Analysis.Complex.OpenMapping',
         'Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt': 'Mathlib.Analysis.Complex.RemovableSingularity',
         'Complex.HadamardThreeLines.verticalStrip': 'Mathlib.Analysis.Complex.Hadamard',
         "Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'": 'Mathlib.Analysis.Complex.Hadamard',
         'herglotzRieszKernel': 'Mathlib.Analysis.Complex.Poisson',
         'poissonKernel': 'Mathlib.Analysis.Complex.Poisson',
         'DiffContOnCl.circleAverage_poissonKernel_smul': 'Mathlib.Analysis.Complex.Poisson',
         'InnerProductSpace.HarmonicOnNhd.circleAverage_eq': 'Mathlib.Analysis.Complex.Harmonic.MeanValue',
         'InnerProductSpace.HarmonicContOnCl.circleAverage_eq': 'Mathlib.Analysis.Complex.Harmonic.MeanValue',
         'InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq': 'Mathlib.Analysis.Complex.Harmonic.Analytic',
         'InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant': 'Mathlib.Analysis.Complex.Harmonic.Liouville',
         'InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul': 'Mathlib.Analysis.Complex.Harmonic.Poisson',
         'InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul': 'Mathlib.Analysis.Complex.Harmonic.Poisson',
         'MeromorphicAt': 'Mathlib.Analysis.Meromorphic.Basic',
         'MeromorphicOn': 'Mathlib.Analysis.Meromorphic.Basic',
         'Meromorphic': 'Mathlib.Analysis.Meromorphic.Basic',
         'MeromorphicNFAt': 'Mathlib.Analysis.Meromorphic.NormalForm',
         'MeromorphicNFOn': 'Mathlib.Analysis.Meromorphic.NormalForm',
         'MeromorphicAt.analyticAt': 'Mathlib.Analysis.Meromorphic.Order',
         'MeromorphicOn.circleAverage_log_norm': 'Mathlib.Analysis.Complex.JensenFormula',
         'AnalyticOnNhd.circleAverage_log_norm': 'Mathlib.Analysis.Complex.JensenFormula',
         'Meromorphic.Gamma': 'Mathlib.Analysis.Meromorphic.Complex',
         'MeromorphicNFOn.Gamma': 'Mathlib.Analysis.Meromorphic.Complex',
         'Meromorphic.logDeriv_mul_eventuallyEq': 'Mathlib.Analysis.Meromorphic.LogDeriv',
         'MeromorphicOn.extract_zeros_poles': 'Mathlib.Analysis.Meromorphic.FactorizedRational',
         'ValueDistribution.characteristic': 'Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction',
         'ValueDistribution.proximity': 'Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic',
         'ValueDistribution.logCounting': 'Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic',
         'ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero': 'Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem',
         'ValueDistribution.characteristic_sub_characteristic_inv_le': 'Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem',
         'ValueDistribution.isBigO_characteristic_sub_characteristic_inv': 'Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem',
         'ValueDistribution.abs_characteristic_sub_characteristic_shift_le': 'Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem',
         'ValueDistribution.isBigO_characteristic_sub_characteristic_moebius': 'Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem',
         'Real.exists_sum_posLog_inv_norm_sub_le': 'Mathlib.Analysis.Complex.ValueDistribution.SecondMainTheorem',
         'UpperHalfPlane': 'Mathlib.Analysis.Complex.UpperHalfPlane.Basic',
         'UpperHalfPlane.dist_log_im_le': 'Mathlib.Analysis.Complex.UpperHalfPlane.Metric',
         'UpperHalfPlane.isometry_vertical_line': 'Mathlib.Analysis.Complex.UpperHalfPlane.Metric',
         'UpperHalfPlane.isometry_real_vadd': 'Mathlib.Analysis.Complex.UpperHalfPlane.Metric',
         'UpperHalfPlane.isometry_pos_mul': 'Mathlib.Analysis.Complex.UpperHalfPlane.Metric',
         'UpperHalfPlane.volume_def': 'Mathlib.Analysis.Complex.UpperHalfPlane.Measure',
         'UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume': 'Mathlib.Analysis.Complex.UpperHalfPlane.Measure',
         'Polynomial.rootSet_derivative_subset_convexHull_rootSet': 'Mathlib.Analysis.Complex.Polynomial.GaussLucas',
         'Polynomial.eq_centerMass_of_eval_derivative_eq_zero': 'Mathlib.Analysis.Complex.Polynomial.GaussLucas'}
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertEqual(origin["package"], "mathlib")
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_complex_analysis_hierarchies_retain_models_and_axiom_paths(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {'Math.ComplexAnalysis.harmonic_poisson_formula': ['InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul',
                                                           'SeparatingDual.eq_iff_forall_dual_eq',
                                                           'ContinuousLinearMap.circleAverage_comp_comm',
                                                           'InnerProductSpace.HarmonicContOnCl.comp_CLM',
                                                           'Real.circleAverage'],
         'Math.ComplexAnalysis.harmonicOnNhd_poisson_formula': ['Math.ComplexAnalysis.harmonic_poisson_formula',
                                                                'InnerProductSpace.HarmonicOnNhd'],
         'Math.ComplexAnalysis.harmonic_eqOn_closedBall_of_eqOn_sphere': ['Math.ComplexAnalysis.harmonic_poisson_formula',
                                                                          'Real.circleAverage_congr_sphere',
                                                                          'InnerProductSpace.HarmonicContOnCl'],
         'Math.ComplexAnalysis.deriv_eq_of_bounded_deriv': ['Differentiable.apply_eq_apply_of_bounded',
                                                            'Differentiable.deriv',
                                                            'Complex.liouville_theorem_aux',
                                                            'Complex.norm_deriv_le_of_forall_mem_sphere_norm_le'],
         'Math.ComplexAnalysis.existsUnique_affine_of_bounded_deriv': ['Math.ComplexAnalysis.eq_smul_deriv_add_of_bounded_deriv',
                                                                       'is_const_of_deriv_eq_zero',
                                                                       'deriv'],
         'Math.ComplexAnalysis.dist_eq_of_bounded_deriv': ['Math.ComplexAnalysis.eq_smul_deriv_add_of_bounded_deriv',
                                                           'NormedSpace'],
         'Math.ComplexAnalysis.isBounded_range_iff_deriv_eq_zero': ['Differentiable.apply_eq_apply_of_bounded',
                                                                    'Bornology.IsBounded',
                                                                    'deriv'],
         'Math.ComplexAnalysis.existsUnique_zero_of_bounded_deriv': ['Math.ComplexAnalysis.surjective_of_bounded_deriv',
                                                                     'Math.ComplexAnalysis.injective_of_bounded_deriv',
                                                                     'Complex'],
         'DiffContOnCl.circleIntegral_sub_inv_smul': ['Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable',
                                                      'DiffContOnCl',
                                                      'circleIntegral'],
         'Complex.hasSum_taylorSeries_of_entire': ['Complex.hasSum_taylorSeries_on_eball', 'iteratedDeriv', 'HasSum'],
         'Complex.norm_deriv_le_one_of_mapsTo_ball': ['_private.Mathlib.Analysis.Complex.Schwarz.0.Complex.schwarz_aux',
                                                      'Complex.norm_fderiv_le_div_of_mapsTo_ball',
                                                      'DifferentiableOn'],
         'Complex.norm_le_of_forall_mem_frontier_norm_le': ['Complex.exists_mem_frontier_isMaxOn_norm',
                                                            'DiffContOnCl',
                                                            'Bornology.IsBounded'],
         "Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'": ['Complex.HadamardThreeLines.verticalClosedStrip',
                                                                                   'Complex.HadamardThreeLines.verticalStrip',
                                                                                   'Real.rpow',
                                                                                   'Complex.exp'],
         'AnalyticOnNhd.eq_of_frequently_eq': ['AnalyticAt.frequently_zero_iff_eventually_zero',
                                               'AnalyticAt',
                                               'ConnectedSpace'],
         'FormalMultilinearSeries.radius_eq_liminf': ['FormalMultilinearSeries.radius',
                                                      'FormalMultilinearSeries',
                                                      'ENNReal'],
         'AnalyticAt.analyticOrderAt_deriv_add_one': ['analyticOrderAt', 'AnalyticAt', 'deriv'],
         'MeromorphicOn.circleAverage_log_norm': ['MeromorphicOn.extract_zeros_poles',
                                                  'meromorphicTrailingCoeffAt',
                                                  'MeromorphicOn.divisor',
                                                  'Real.circleAverage'],
         'Meromorphic.Gamma': ['MeromorphicNFOn.Gamma', 'Complex.differentiable_one_div_Gamma', 'Meromorphic'],
         'ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero': ['MeromorphicOn.circleAverage_log_norm',
                                                                                'ValueDistribution.characteristic',
                                                                                'ValueDistribution.logCounting',
                                                                                'ValueDistribution.proximity'],
         'ValueDistribution.abs_characteristic_sub_characteristic_shift_le': ['ValueDistribution.proximity',
                                                                              'ValueDistribution.characteristic',
                                                                              'Meromorphic'],
         'InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant': ['InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq',
                                                                             'Differentiable.apply_eq_apply_of_bounded',
                                                                             'InnerProductSpace.HarmonicOnNhd'],
         'InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul': ['poissonKernel',
                                                                                 'Real.circleAverage',
                                                                                 'InnerProductSpace.HarmonicContOnCl'],
         'UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume': ['MeasureTheory.SMulInvariantMeasure',
                                                                                            'MeasureTheory.Measure',
                                                                                            'UpperHalfPlane'],
         'Polynomial.rootSet_derivative_subset_convexHull_rootSet': ['Polynomial.eq_centerMass_of_eval_derivative_eq_zero',
                                                                     'Finset.centerMass',
                                                                     'convexHull']}
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_complex_analysis_subjects_retain_results_and_ancestors(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {'analytic_functions': ('analysis', 'AnalyticOnNhd.eq_of_frequently_eq'),
         'complex_integration': ('complex_analysis', 'DiffContOnCl.circleIntegral_sub_inv_smul'),
         'holomorphic_functions': ('complex_analysis', 'Math.ComplexAnalysis.existsUnique_affine_of_bounded_deriv'),
         'meromorphic_functions': ('complex_analysis', 'Meromorphic.Gamma'),
         'value_distribution': ('meromorphic_functions',
                                'ValueDistribution.characteristic_sub_characteristic_inv_le'),
         'harmonic_functions': ('complex_analysis',
                                'InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant'),
         'hyperbolic_geometry': ('geometry', 'UpperHalfPlane.dist_log_im_le'),
         'complex_polynomials': ('complex_analysis', 'Polynomial.rootSet_derivative_subset_convexHull_rootSet')}
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                current = subject
                while current is not None:
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=current)})
                    current = self.catalog["subjects"][current]["parent"]

    def test_entire_affine_results_retain_local_proofs_and_source(self):
        names = ['Math.ComplexAnalysis.bijective_of_bounded_deriv',
         'Math.ComplexAnalysis.deriv_eq_of_bounded_deriv',
         'Math.ComplexAnalysis.dist_eq_of_bounded_deriv',
         'Math.ComplexAnalysis.eq_smul_deriv_add_of_bounded_deriv',
         'Math.ComplexAnalysis.existsUnique_affine_of_bounded_deriv',
         'Math.ComplexAnalysis.existsUnique_zero_of_bounded_deriv',
         'Math.ComplexAnalysis.injective_of_bounded_deriv',
         'Math.ComplexAnalysis.isBounded_range_iff_deriv_eq_zero',
         'Math.ComplexAnalysis.lipschitzWith_of_bounded_deriv',
         'Math.ComplexAnalysis.norm_le_of_bounded_deriv',
         'Math.ComplexAnalysis.surjective_of_bounded_deriv']
        module = "Math.Analysis.EntireAffine"
        path = ROOT / "Math/Analysis/EntireAffine.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        for name in names:
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))

    def test_banach_harmonic_poisson_results_retain_proofs_and_source(self):
        names = [
            "Math.ComplexAnalysis.harmonic_poisson_formula",
            "Math.ComplexAnalysis.harmonicOnNhd_poisson_formula",
            "Math.ComplexAnalysis.harmonic_eqOn_closedBall_of_eqOn_sphere",
        ]
        module = "Math.Analysis.HarmonicPoisson"
        path = ROOT / "Math/Analysis/HarmonicPoisson.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        graph = KnowledgeGraph(self.catalog)
        for name in names:
            with self.subTest(name=name):
                node = self.nodes[name]
                self.assertIn(name, self.catalog["roots"])
                self.assertEqual(node["module"], module)
                self.assertEqual(node["kind"], "theorem")
                self.assertIsInstance(node["value"], int)
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                for subject in ("harmonic_functions", "complex_analysis", "partial_differential_equations", "mathematics"):
                    self.assertIn(name, {item["name"] for item in graph.search(name, subject=subject)})

    def test_value_distribution_references_retain_pinned_bibliography_records(self):
        snapshot = open_snapshot(ROOT)
        for name in ("ValueDistribution.characteristic", "ValueDistribution.characteristic_sub_characteristic_inv_le"):
            with self.subTest(name=name):
                references = snapshot.citations(name)
                resolved = {entry["key"] for entry in references["module_citations"]}
                self.assertTrue({"MR886677", "MR3156076"} <= resolved)

    def test_unfinished_complex_modules_are_identified_as_preparations(self):
        for module in ("Mathlib.Analysis.Complex.RiemannMapping",
                       "Mathlib.Analysis.Complex.ValueDistribution.SecondMainTheorem"):
            with self.subTest(module=module):
                self.assertIn("preparations", self.catalog["module_policy"][module]["title"])
                selected = set(self.catalog["module_declarations_by_module"][module]) & set(self.catalog["roots"])
                self.assertTrue(selected)
                self.assertTrue(any(self.nodes[name]["kind"] == "theorem" for name in selected))

    def test_harmonic_analysis_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/HarmonicAnalysisStatements.lean"], capture=True)

    def test_harmonic_analysis_covers_every_module_in_its_pinned_directories(self):
        base = ROOT / ".lake/packages/mathlib"
        directories = ("Mathlib/Analysis/Fourier", "Mathlib/Analysis/Distribution",
                       "Mathlib/Analysis/SpecialFunctions/Gaussian")
        expected = {".".join(path.relative_to(base).with_suffix("").parts)
                    for directory in directories for path in (base / directory).rglob("*.lean")}
        prefixes = tuple(directory.replace("/", ".") + "." for directory in directories)
        registered = self.policy["libraries"]["mathlib"]["modules"]
        self.assertEqual({name for name in registered if name.startswith(prefixes)}, expected)
        self.assertEqual(len(expected), 30)
        for module in expected:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                self.assertIn(module, self.catalog["sources"])

    def test_harmonic_analysis_objects_retain_terms_and_pinned_sources(self):
        expected = {
            "FourierTransform": "Mathlib.Analysis.Fourier.Notation",
            "FourierTransform.fourierEquiv": "Mathlib.Analysis.Fourier.Notation",
            "MeasureTheory.Integrable.fourierInv_fourier_eq": "Mathlib.Analysis.Fourier.Inversion",
            "Continuous.fourierInv_fourier_eq": "Mathlib.Analysis.Fourier.Inversion",
            "MeasureTheory.Lp.fourierTransformₗᵢ": "Mathlib.Analysis.Fourier.LpSpace",
            "MeasureTheory.Lp.norm_fourier_eq": "Mathlib.Analysis.Fourier.LpSpace",
            "MeasureTheory.Lp.inner_fourier_eq": "Mathlib.Analysis.Fourier.LpSpace",
            "SchwartzMap.toLp_fourier_eq": "Mathlib.Analysis.Fourier.LpSpace",
            "MeasureTheory.Lp.fourier_toTemperedDistribution_eq": "Mathlib.Analysis.Fourier.LpSpace",
            "Real.fourier_mul_convolution_eq": "Mathlib.Analysis.Fourier.Convolution",
            "SchwartzMap.convolution": "Mathlib.Analysis.Fourier.Convolution",
            "SchwartzMap.fourier_convolution": "Mathlib.Analysis.Fourier.Convolution",
            "SchwartzMap.convolution_apply": "Mathlib.Analysis.Fourier.Convolution",
            "fourierBasis": "Mathlib.Analysis.Fourier.AddCircle",
            "fourierCoeff": "Mathlib.Analysis.Fourier.AddCircle",
            "hasSum_fourier_series_L2": "Mathlib.Analysis.Fourier.AddCircle",
            "tsum_sq_fourierCoeff": "Mathlib.Analysis.Fourier.AddCircle",
            "SchwartzMap.tsum_eq_tsum_fourier": "Mathlib.Analysis.Fourier.PoissonSummation",
            "Real.tsum_eq_tsum_fourier_of_rpow_decay": "Mathlib.Analysis.Fourier.PoissonSummation",
            "ZMod.dft": "Mathlib.Analysis.Fourier.ZMod",
            "ZMod.dft_dft": "Mathlib.Analysis.Fourier.ZMod",
            "AddChar.complexBasis": "Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality",
            "AddChar.doubleDualEquiv": "Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality",
            "AddChar.wInner_cWeight_eq_boole": "Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality",
            "Real.zero_at_infty_fourier": "Mathlib.Analysis.Fourier.RiemannLebesgueLemma",
            "SchwartzMap": "Mathlib.Analysis.Distribution.SchwartzSpace.Basic",
            "SchwartzMap.fourierTransformCLM": "Mathlib.Analysis.Distribution.SchwartzSpace.Fourier",
            "SchwartzMap.integral_norm_sq_fourier": "Mathlib.Analysis.Distribution.SchwartzSpace.Fourier",
            "SchwartzMap.norm_fourier_toL2_eq": "Mathlib.Analysis.Distribution.SchwartzSpace.Fourier",
            "SchwartzMap.fourier_lineDerivOp_eq": "Mathlib.Analysis.Distribution.SchwartzSpace.Fourier",
            "Distribution": "Mathlib.Analysis.Distribution.Distribution",
            "Distribution.ofFun": "Mathlib.Analysis.Distribution.Distribution",
            "Distribution.delta": "Mathlib.Analysis.Distribution.Distribution",
            "Distribution.lineDerivCLM": "Mathlib.Analysis.Distribution.Distribution",
            "Distribution.lineDerivOp_apply_apply": "Mathlib.Analysis.Distribution.Distribution",
            "Distribution.ofFun_injective": "Mathlib.Analysis.Distribution.Distribution",
            "TestFunction": "Mathlib.Analysis.Distribution.TestFunction",
            "TemperedDistribution": "Mathlib.Analysis.Distribution.TemperedDistribution",
            "TemperedDistribution.delta": "Mathlib.Analysis.Distribution.TemperedDistribution",
            "TemperedDistribution.fourier_delta_zero": "Mathlib.Analysis.Distribution.TemperedDistribution",
            "MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot": "Mathlib.Analysis.Distribution.TemperedDistribution",
            "TemperedDistribution.fourierMultiplierCLM": "Mathlib.Analysis.Distribution.FourierMultiplier",
            "TemperedDistribution.laplacian_eq_fourierMultiplierCLM": "Mathlib.Analysis.Distribution.FourierMultiplier",
            "TemperedDistribution.besselPotential": "Mathlib.Analysis.Distribution.Sobolev",
            "TemperedDistribution.MemSobolev": "Mathlib.Analysis.Distribution.Sobolev",
            "SchwartzMap.memSobolev": "Mathlib.Analysis.Distribution.Sobolev",
            "TemperedDistribution.MemSobolev.lineDerivOp": "Mathlib.Analysis.Distribution.Sobolev",
            "TemperedDistribution.MemSobolev.laplacian": "Mathlib.Analysis.Distribution.Sobolev",
            "TemperedDistribution.MemSobolev.fourier_memL1": "Mathlib.Analysis.Distribution.Sobolev",
            "Distribution.dsupport": "Mathlib.Analysis.Distribution.Support",
            "Distribution.TemperedDistribution.dsupport_delta": "Mathlib.Analysis.Distribution.Support",
            "Distribution.TemperedDistribution.dsupport_lineDerivOp_subset": "Mathlib.Analysis.Distribution.Support",
            "integral_gaussian": "Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral",
            "fourier_gaussian_pi": "Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform",
            "GaussianFourier.integral_rexp_neg_mul_sq_norm": "Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform",
            "Real.tsum_exp_neg_mul_int_sq": "Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation",
            "Complex.tsum_exp_neg_quadratic": "Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation"
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertEqual(origin["package"], "mathlib")
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_harmonic_analysis_hierarchies_retain_models_and_axiom_paths(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "Math.HarmonicAnalysis.existsUnique_elliptic_solution": [
                "Math.HarmonicAnalysis.besselPotential_two_eq",
                "Math.HarmonicAnalysis.eq_ellipticSolution",
                "TemperedDistribution.besselPotential",
                "TemperedDistribution.fourierMultiplierCLM",
                "TemperedDistribution"
            ],
            "Math.HarmonicAnalysis.ellipticSolution_memSobolev_iff": [
                "TemperedDistribution.MemSobolev",
                "TemperedDistribution.besselPotential_besselPotential_apply",
                "Math.HarmonicAnalysis.ellipticSolution"
            ],
            "Math.HarmonicAnalysis.fourier_ellipticSolution": [
                "TemperedDistribution.besselPotential",
                "TemperedDistribution.fourierMultiplierCLM",
                "TemperedDistribution.smulLeftCLM"
            ],
            "Math.HarmonicAnalysis.besselPotentialEquiv": [
                "TemperedDistribution.besselPotential",
                "ContinuousLinearEquiv.equivOfInverse",
                "TemperedDistribution.besselPotential_besselPotential_apply"
            ],
            "MeasureTheory.Integrable.fourierInv_fourier_eq": [
                "Real.tendsto_integral_gaussian_smul",
                "GaussianFourier.integral_rexp_neg_mul_sq_norm",
                "MeasureTheory.Integrable",
                "ContinuousAt"
            ],
            "MeasureTheory.Lp.norm_fourier_eq": [
                "MeasureTheory.Lp.fourierTransformₗᵢ",
                "SchwartzMap.norm_fourier_toL2_eq",
                "SchwartzMap.toLpCLM",
                "SchwartzMap"
            ],
            "Real.fourier_mul_convolution_eq": [
                "Real.fourier_bilin_convolution_eq",
                "MeasureTheory.Integrable",
                "ContinuousLinearMap"
            ],
            "SchwartzMap.tsum_eq_tsum_fourier": [
                "Real.tsum_eq_tsum_fourier_of_rpow_decay",
                "SchwartzMap.isBigO_cocompact_rpow",
                "SchwartzMap"
            ],
            "tsum_sq_fourierCoeff": [
                "fourierBasis",
                "HilbertBasis",
                "MeasureTheory.Lp"
            ],
            "ZMod.dft_dft": [
                "ZMod.dft",
                "ZMod",
                "Complex"
            ],
            "AddChar.doubleDualEquiv": [
                "AddChar.doubleDualEmb",
                "AddChar.complexBasis",
                "AddChar"
            ],
            "TemperedDistribution.MemSobolev.laplacian": [
                "TemperedDistribution.besselPotential_neg_two_laplacian_eq",
                "TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded",
                "TemperedDistribution.MemSobolev"
            ],
            "Distribution.TemperedDistribution.dsupport_delta": [
                "TemperedDistribution.delta",
                "Distribution.dsupport",
                "SchwartzMap"
            ],
            "Distribution.lineDerivOp_apply_apply": [
                "Distribution.lineDerivCLM",
                "TestFunction",
                "Distribution"
            ],
            "Real.tsum_exp_neg_mul_int_sq": [
                "fourier_gaussian_pi'",
                "Real.tsum_eq_tsum_fourier_of_rpow_decay",
                "Complex.exp"
            ]
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(set(objects) <= reached, set(objects) - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_harmonic_analysis_subjects_retain_results_and_ancestors(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "harmonic_analysis": ("analysis", "Math.HarmonicAnalysis.existsUnique_elliptic_solution"),
            "fourier_analysis": ("harmonic_analysis", "MeasureTheory.Lp.norm_fourier_eq"),
            "fourier_series": ("fourier_analysis", "tsum_sq_fourierCoeff"),
            "finite_fourier_analysis": ("fourier_analysis", "AddChar.doubleDualEquiv"),
            "distribution_theory": ("harmonic_analysis", "Distribution.lineDerivOp_apply_apply"),
            "schwartz_spaces": ("distribution_theory", "SchwartzMap.fourierTransformCLM"),
            "sobolev_spaces": ("distribution_theory", "TemperedDistribution.MemSobolev.laplacian"),
            "partial_differential_equations": ("analysis", "Math.HarmonicAnalysis.existsUnique_elliptic_solution"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "harmonic_analysis", "analysis", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_distribution_references_retain_their_pinned_bibliography_records(self):
        snapshot = open_snapshot(ROOT)
        expected = {
            "Distribution": {"schwartz1950", "schwartz1957", "hormander2003"},
            "TemperedDistribution.MemSobolev": {"taylorPDE1", "mclean2000"},
        }
        for name, keys in expected.items():
            with self.subTest(name=name):
                references = snapshot.citations(name)
                resolved = {entry["key"] for entry in references["module_citations"]}
                self.assertTrue(keys <= resolved, keys - resolved)

    def test_elliptic_solutions_retain_local_proofs_and_source(self):
        names = [
            "Math.HarmonicAnalysis.besselPotentialEquiv",
            "Math.HarmonicAnalysis.besselPotentialEquiv_apply",
            "Math.HarmonicAnalysis.besselPotentialEquiv_symm_apply",
            "Math.HarmonicAnalysis.fourierMultiplier_add",
            "Math.HarmonicAnalysis.besselPotential_two_eq",
            "Math.HarmonicAnalysis.ellipticSolution",
            "Math.HarmonicAnalysis.ellipticSolution_spec",
            "Math.HarmonicAnalysis.eq_ellipticSolution",
            "Math.HarmonicAnalysis.existsUnique_elliptic_solution",
            "Math.HarmonicAnalysis.ellipticSolution_zero",
            "Math.HarmonicAnalysis.ellipticSolution_add",
            "Math.HarmonicAnalysis.ellipticSolution_smul",
            "Math.HarmonicAnalysis.continuous_ellipticSolution",
            "Math.HarmonicAnalysis.fourier_ellipticSolution",
            "Math.HarmonicAnalysis.elliptic_homogeneous_iff",
            "Math.HarmonicAnalysis.ellipticSolution_memSobolev_iff",
            "Math.HarmonicAnalysis.ellipticSolution_memSobolev"
        ]
        module = "Math.Analysis.BesselEquation"
        path = ROOT / "Math/Analysis/BesselEquation.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        for name in names:
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
        graph = KnowledgeGraph(self.catalog)
        name = "Math.HarmonicAnalysis.existsUnique_elliptic_solution"
        for subject in ("harmonic_analysis", "fourier_analysis", "distribution_theory", "sobolev_spaces",
                        "partial_differential_equations", "analysis", "mathematics"):
            self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_functional_analysis_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/FunctionalAnalysisStatements.lean"], capture=True)

    def test_functional_analysis_covers_every_module_in_its_pinned_directories(self):
        base = ROOT / ".lake/packages/mathlib"
        directories = ("Mathlib/Analysis/InnerProductSpace", "Mathlib/Analysis/Normed/Operator",
                       "Mathlib/Analysis/Normed/Algebra", "Mathlib/Analysis/Normed/Module",
                       "Mathlib/Analysis/LocallyConvex")
        expected = {".".join(path.relative_to(base).with_suffix("").parts)
                    for directory in directories for path in (base / directory).rglob("*.lean")}
        registered = self.policy["libraries"]["mathlib"]["modules"]
        prefixes = tuple(directory.replace("/", ".") + "." for directory in directories)
        actual = {name for name in registered if name.startswith(prefixes)}
        self.assertEqual(actual, expected)
        self.assertEqual(len(expected), 148)
        for module in expected:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["module_declarations_by_module"])
                self.assertIn(module, self.catalog["sources"])

    def test_functional_analysis_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "NormedSpace": "Mathlib.Analysis.Normed.Module.Basic",
            "InnerProductSpace": "Mathlib.Analysis.InnerProductSpace.Defs",
            "NormedAlgebra": "Mathlib.Analysis.Normed.Module.Basic",
            "IsCoercive": "Mathlib.Analysis.Normed.Operator.NormedSpace",
            "IsCompactOperator": "Mathlib.Analysis.Normed.Operator.Compact.Basic",
            "ContinuousLinearMap.IsFredholm": "Mathlib.Analysis.Normed.Operator.Fredholm.Basic",
            "ContinuousLinearMap.FredholmPackage": "Mathlib.Analysis.Normed.Operator.Fredholm.Basic",
            "exists_extension_norm_eq": "Mathlib.Analysis.Normed.Module.HahnBanach",
            "exists_dual_vector": "Mathlib.Analysis.Normed.Module.HahnBanach",
            "banach_steinhaus": "Mathlib.Analysis.Normed.Operator.BanachSteinhaus",
            "ContinuousLinearMap.isOpenMap": "Mathlib.Analysis.Normed.Operator.Banach",
            "ContinuousLinearEquiv.ofBijective": "Mathlib.Analysis.Normed.Operator.Banach",
            "LinearMap.continuous_of_isClosed_graph": "Mathlib.Analysis.Normed.Operator.Banach",
            "LinearMap.continuous_of_seq_closed_graph": "Mathlib.Analysis.Normed.Operator.Banach",
            "exists_norm_eq_iInf_of_complete_convex": "Mathlib.Analysis.InnerProductSpace.Projection.Minimal",
            "Submodule.exists_norm_eq_iInf_of_complete_subspace": "Mathlib.Analysis.InnerProductSpace.Projection.Minimal",
            "Submodule.orthogonalProjectionOnto": "Mathlib.Analysis.InnerProductSpace.Projection.Basic",
            "InnerProductSpace.toDual": "Mathlib.Analysis.InnerProductSpace.Dual",
            "InnerProductSpace.toDual_symm_apply": "Mathlib.Analysis.InnerProductSpace.Dual",
            "IsCoercive.continuousLinearEquivOfBilin": "Mathlib.Analysis.InnerProductSpace.LaxMilgram",
            "IsCoercive.continuousLinearEquivOfBilin_apply": "Mathlib.Analysis.InnerProductSpace.LaxMilgram",
            "ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection": "Mathlib.Analysis.InnerProductSpace.MeanErgodic",
            "ContinuousLinearMap.adjoint": "Mathlib.Analysis.InnerProductSpace.Adjoint",
            "LinearMap.IsSymmetric.eigenvectorBasis": "Mathlib.Analysis.InnerProductSpace.Spectrum",
            "LinearMap.IsSymmetric.apply_eigenvectorBasis": "Mathlib.Analysis.InnerProductSpace.Spectrum",
            "ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot": "Mathlib.Analysis.InnerProductSpace.Spectrum",
            "ContinuousLinearMap.finite_dimensional_eigenspace": "Mathlib.Analysis.InnerProductSpace.Spectrum",
            "LinearMap.singularValues": "Mathlib.Analysis.InnerProductSpace.SingularValues",
            "LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues": "Mathlib.Analysis.InnerProductSpace.SingularValues",
            "LinearMap.card_support_singularValues": "Mathlib.Analysis.InnerProductSpace.SingularValues",
            "IsCompactOperator.hasEigenvalue_or_mem_resolventSet": "Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative",
            "IsCompactOperator.hasEigenvalue_iff_mem_spectrum": "Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative",
            "ContinuousLinearMap.isOpen_setOfPred_isFredholm": "Mathlib.Analysis.Normed.Operator.Fredholm.Open",
            "ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq": "Mathlib.Analysis.Normed.Operator.Fredholm.Open",
            "WeakDual.isCompact_closedBall": "Mathlib.Analysis.Normed.Module.WeakDual",
            "WeakDual.isCompact_polar": "Mathlib.Analysis.Normed.Module.WeakDual",
            "geometric_hahn_banach_compact_closed": "Mathlib.Analysis.LocallyConvex.Separation",
            "geometric_hahn_banach_point_closed": "Mathlib.Analysis.LocallyConvex.Separation",
            "Convex.toWeakSpace_closure": "Mathlib.Analysis.LocallyConvex.WeakSpace",
            "spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius": "Mathlib.Analysis.Normed.Algebra.GelfandFormula",
            "spectrum.nonempty": "Mathlib.Analysis.Normed.Algebra.GelfandFormula",
            "spectrum.map_polynomial_aeval": "Mathlib.Analysis.Normed.Algebra.GelfandFormula",
            "NormedRing.algEquivComplexOfComplete": "Mathlib.Analysis.Normed.Algebra.GelfandFormula",
            "NormedAlgebra.Complex.nonempty_algEquiv": "Mathlib.Analysis.Normed.Algebra.GelfandMazur",
            "NormedAlgebra.Real.nonempty_algEquiv_or": "Mathlib.Analysis.Normed.Algebra.GelfandMazur",
            "NormedSpace.exp": "Mathlib.Analysis.Normed.Algebra.Exponential",
            "NormedSpace.exp_add_of_commute": "Mathlib.Analysis.Normed.Algebra.Exponential",
            "PiTensorProduct.projectiveSeminorm": "Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm",
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_functional_analysis_hierarchies_reach_models_hypotheses_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "Math.FunctionalAnalysis.existsUnique_weak_solution": {
                "InnerProductSpace.toDual",
                "IsCoercive.continuousLinearEquivOfBilin",
                "Math.FunctionalAnalysis.weakSolutionEquiv",
                "ContinuousLinearEquiv.ofBijective",
                "CompleteSpace",
            },
            "Math.FunctionalAnalysis.norm_weakSolution_le": {
                "IsCoercive",
                "ContinuousLinearMap.le_opNorm",
                "Math.FunctionalAnalysis.bilinear_weakSolution",
            },
            "Math.FunctionalAnalysis.dist_weakSolution_le": {
                "Math.FunctionalAnalysis.norm_weakSolution_le",
                "Math.FunctionalAnalysis.weakSolution_sub",
                "Math.FunctionalAnalysis.weakSolutionEquiv",
            },
            "ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection": {
                "birkhoffAverage",
                "Submodule.orthogonalProjectionOnto",
                "InnerProductSpace",
                "CompleteSpace",
                "LinearMap.eqLocus",
            },
            "exists_extension_norm_eq": {
                "StrongDual",
                "Module.Dual.exists_continuous_extension_of_le_seminorm",
                "IsRCLikeNormedField",
            },
            "ContinuousLinearMap.isOpenMap": {
                "ContinuousLinearMap",
                "Metric.isOpen_iff",
                "nonempty_interior_of_iUnion_of_closed",
                "CompleteSpace",
            },
            "IsCompactOperator.hasEigenvalue_or_mem_resolventSet": {
                "IsCompactOperator",
                "Module.End.HasEigenvalue",
                "resolventSet",
                "IsCompactOperator.antilipschitz_of_not_hasEigenvalue",
            },
            "WeakDual.isCompact_closedBall": {
                "WeakDual",
                "IsCompact",
                "ProperSpace",
                "WeakDual.toStrongDual",
                "Metric.closedBall",
            },
            "spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius": {
                "spectralRadius",
                "Filter.Tendsto",
                "NormedAlgebra",
                "Complex",
            },
            "LinearMap.IsSymmetric.apply_eigenvectorBasis": {
                "LinearMap.IsSymmetric",
                "OrthonormalBasis",
                "Module.End.HasEigenvector",
                "FiniteDimensional",
            },
            "ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot": {
                "IsCompactOperator",
                "Submodule.orthogonal",
                "Module.End.eigenspace",
                "InnerProductSpace",
            },
            "ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq": {
                "ContinuousLinearMap.IsFredholm",
                "LinearMap.index",
                "ContinuousLinearMap.FredholmPackage",
                "CompleteSpace",
            },
            "geometric_hahn_banach_compact_closed": {
                "Convex",
                "ContinuousLinearMap",
                "LocallyConvexSpace",
            },
            "LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues": {
                "LinearMap.singularValues",
                "LinearMap.adjoint",
                "Module.End.HasEigenvalue",
                "Real.sqrt",
            },
            "banach_steinhaus": {
                "ContinuousLinearMap",
                "CompleteSpace",
                "WithSeminorms.banach_steinhaus",
                "Bornology.IsVonNBounded",
            },
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_functional_analysis_subjects_include_their_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "functional_analysis": ("analysis", "Math.FunctionalAnalysis.existsUnique_weak_solution"),
            "hilbert_spaces": ("functional_analysis", "InnerProductSpace.toDual"),
            "operator_theory": ("functional_analysis", "ContinuousLinearMap.isOpenMap"),
            "compact_operators": ("operator_theory", "IsCompactOperator.hasEigenvalue_iff_mem_spectrum"),
            "fredholm_operators": ("operator_theory", "ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq"),
            "normed_algebras": ("functional_analysis", "spectrum.nonempty"),
            "locally_convex_spaces": ("functional_analysis", "geometric_hahn_banach_compact_closed"),
            "dual_spaces": ("functional_analysis", "exists_extension_norm_eq"),
            "spectral_theory": ("operator_theory", "ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "functional_analysis", "analysis", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_functional_analysis_references_link_their_pinned_records(self):
        snapshot = open_snapshot(ROOT)
        expected = {
            "LinearMap.singularValues": "axler2024",
            "NormedAlgebra.Complex.nonempty_algEquiv": "ostrowski1916",
            "IsCoercive.continuousLinearEquivOfBilin": "howard",
        }
        for name, key in expected.items():
            with self.subTest(name=name):
                references = snapshot.citations(name)
                self.assertIn(key, {entry["key"] for entry in references["module_citations"]})

    def test_lax_milgram_weak_solutions_retain_local_proofs_and_source(self):
        names = [
            "Math.FunctionalAnalysis.weakSolutionEquiv",
            "Math.FunctionalAnalysis.weakSolution",
            "Math.FunctionalAnalysis.bilinear_weakSolution",
            "Math.FunctionalAnalysis.eq_weakSolution",
            "Math.FunctionalAnalysis.existsUnique_weak_solution",
            "Math.FunctionalAnalysis.weakSolution_zero",
            "Math.FunctionalAnalysis.weakSolution_add",
            "Math.FunctionalAnalysis.weakSolution_sub",
            "Math.FunctionalAnalysis.weakSolution_smul",
            "Math.FunctionalAnalysis.continuous_weakSolution",
            "Math.FunctionalAnalysis.norm_weakSolution_le",
            "Math.FunctionalAnalysis.dist_weakSolution_le",
        ]
        module = "Math.Analysis.LaxMilgram"
        path = ROOT / "Math/Analysis/LaxMilgram.lean"
        origin = self.catalog["sources"][module]
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        for name in names:
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertGreater(node["source"]["line"], 0)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
        graph = KnowledgeGraph(self.catalog)
        name = "Math.FunctionalAnalysis.existsUnique_weak_solution"
        for subject in ("functional_analysis", "hilbert_spaces", "dual_spaces", "analysis", "mathematics"):
            self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_dynamics_statements_match_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/DynamicsStatements.lean"], capture=True)

    def test_dynamics_cover_every_pinned_dynamics_and_ode_module(self):
        base = ROOT / ".lake/packages/mathlib"
        paths = list((base / "Mathlib/Dynamics").rglob("*.lean"))
        paths.extend((base / "Mathlib/Analysis/ODE").rglob("*.lean"))
        expected = {".".join(path.relative_to(base).with_suffix("").parts) for path in paths}
        registered = self.policy["libraries"]["mathlib"]["modules"]
        actual = {name for name in registered
                  if name.startswith(("Mathlib.Dynamics.", "Mathlib.Analysis.ODE."))}
        self.assertEqual(actual, expected)
        self.assertEqual(len(expected), 41)
        for module in expected:
            with self.subTest(module=module):
                self.assertIn(module, self.catalog["module_policy"])
                self.assertIn(module, self.catalog["sources"])

    def test_dynamics_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "IsIntegralCurve": "Mathlib.Analysis.ODE.Basic",
            "IsIntegralCurveOn": "Mathlib.Analysis.ODE.Basic",
            "IsPicardLindelof": "Mathlib.Analysis.ODE.PicardLindelof",
            "ODE.picard": "Mathlib.Analysis.ODE.PicardLindelof",
            "IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt": "Mathlib.Analysis.ODE.ExistUnique",
            "IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn": "Mathlib.Analysis.ODE.ExistUnique",
            "ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀": "Mathlib.Analysis.ODE.ExistUnique",
            "ODE_solution_unique_univ": "Mathlib.Analysis.ODE.ExistUnique",
            "gronwallBound": "Mathlib.Analysis.ODE.Gronwall",
            "norm_le_gronwallBound_of_norm_deriv_right_le": "Mathlib.Analysis.ODE.Gronwall",
            "discrete_gronwall": "Mathlib.Analysis.ODE.DiscreteGronwall",
            "Function.fixedPoints": "Mathlib.Dynamics.FixedPoints.Defs",
            "Function.IsPeriodicPt": "Mathlib.Dynamics.PeriodicPts.Defs",
            "Function.IsPeriodicPt.add": "Mathlib.Dynamics.PeriodicPts.Defs",
            "Flow": "Mathlib.Dynamics.Flow",
            "Flow.map_add": "Mathlib.Dynamics.Flow",
            "omegaLimit": "Mathlib.Dynamics.OmegaLimit",
            "isClosed_omegaLimit": "Mathlib.Dynamics.OmegaLimit",
            "MulAction.IsMinimal": "Mathlib.Dynamics.Minimal",
            "MulAction.IsTopologicallyTransitive": "Mathlib.Dynamics.Transitive",
            "Polynomial.newtonMap": "Mathlib.Dynamics.Newton",
            "Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero": "Mathlib.Dynamics.Newton",
            "birkhoffSum": "Mathlib.Dynamics.BirkhoffSum.Basic",
            "birkhoffAverage": "Mathlib.Dynamics.BirkhoffSum.Average",
            "MeasureTheory.Conservative": "Mathlib.Dynamics.Ergodic.Conservative",
            "MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem": "Mathlib.Dynamics.Ergodic.Conservative",
            "Ergodic": "Mathlib.Dynamics.Ergodic.Ergodic",
            "PreErgodic.prob_eq_zero_or_one": "Mathlib.Dynamics.Ergodic.Ergodic",
            "MeasureTheory.empiricalMeasure": "Mathlib.Dynamics.Ergodic.EmpiricalMeasure",
            "MeasureTheory.exists_measurePreserving_probabilityMeasure": "Mathlib.Dynamics.Ergodic.EmpiricalMeasure",
            "Ergodic.iff_mem_extremePoints": "Mathlib.Dynamics.Ergodic.Extreme",
            "AddCircle.ergodic_add_left": "Mathlib.Dynamics.Ergodic.AddCircleAdd",
            "AddCircle.ergodic_nsmul": "Mathlib.Dynamics.Ergodic.AddCircle",
            "CircleDeg1Lift": "Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber",
            "CircleDeg1Lift.translationNumber": "Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber",
            "CircleDeg1Lift.translationNumber_eq_rat_iff": "Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber",
            "Dynamics.coverEntropy": "Mathlib.Dynamics.TopologicalEntropy.CoverEntropy",
            "Dynamics.netEntropyEntourage": "Mathlib.Dynamics.TopologicalEntropy.NetEntropy",
            "Dynamics.coverEntropy_eq_iSup_netEntropyEntourage": "Mathlib.Dynamics.TopologicalEntropy.NetEntropy",
            "Dynamics.coverEntropy_image_le_of_uniformContinuous": "Mathlib.Dynamics.TopologicalEntropy.Semiconj",
            "Dynamics.coverEntropy_restrict": "Mathlib.Dynamics.TopologicalEntropy.Semiconj",
            "SymbolicDynamics.FullShift.Pattern": "Mathlib.Dynamics.SymbolicDynamics.Basic",
            "SymbolicDynamics.FullShift.MulSubshift": "Mathlib.Dynamics.SymbolicDynamics.Basic",
            "SymbolicDynamics.FullShift.mulForbidden": "Mathlib.Dynamics.SymbolicDynamics.Basic",
            "SymbolicDynamics.FullShift.isClosed_mulForbidden": "Mathlib.Dynamics.SymbolicDynamics.Basic",
        }
        for name, module in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][module]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_dynamics_hierarchies_reach_models_hypotheses_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt": {
                "IsPicardLindelof",
                "ODE.picard",
                "ContractingWith",
                "CompleteSpace",
                "HasDerivWithinAt",
            },
            "ODE_solution_unique_univ": {
                "LipschitzOnWith",
                "HasDerivAt",
                "gronwallBound",
                "Real.exp",
            },
            "MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem": {
                "MeasureTheory.Conservative",
                "MeasureTheory.Measure",
                "Nat.iterate",
                "Filter.Frequently",
            },
            "MeasureTheory.exists_measurePreserving_probabilityMeasure": {
                "MeasureTheory.empiricalMeasure",
                "MeasureTheory.ProbabilityMeasure",
                "MeasureTheory.MeasurePreserving",
                "Continuous",
            },
            "Dynamics.coverEntropy_image_le_of_uniformContinuous": {
                "Dynamics.coverEntropy",
                "Dynamics.coverMincard",
                "UniformContinuous",
                "Function.Semiconj",
                "Dynamics.dynEntourage",
            },
            "AddCircle.ergodic_add_left": {
                "AddCircle",
                "Ergodic",
                "addOrderOf",
            },
            "CircleDeg1Lift.translationNumber_eq_rat_iff": {
                "CircleDeg1Lift.translationNumber",
                "CircleDeg1Lift",
                "Continuous",
                "Nat.iterate",
            },
            "Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero": {
                "Polynomial.newtonMap",
                "IsNilpotent",
                "IsUnit",
                "Polynomial.aeval",
            },
            "SymbolicDynamics.FullShift.isClosed_mulForbidden": {
                "SymbolicDynamics.FullShift.Pattern",
                "SymbolicDynamics.FullShift.mulForbidden",
                "SymbolicDynamics.FullShift.Pattern.mulOccursInAt",
                "IsClosed",
                "DiscreteTopology",
            },
            "Ergodic.iff_mem_extremePoints": {
                "Ergodic",
                "Set.extremePoints",
                "MeasureTheory.MeasurePreserving",
            },
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_dynamics_subjects_include_their_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "dynamical_systems": ("analysis", "Polynomial.newtonMap"),
            "ordinary_differential_equations": ("dynamical_systems", "ODE_solution_unique_univ"),
            "topological_dynamics": ("dynamical_systems", "Flow.map_add"),
            "ergodic_theory": ("dynamical_systems", "Ergodic.iff_mem_extremePoints"),
            "symbolic_dynamics": ("topological_dynamics", "SymbolicDynamics.FullShift.mulForbidden"),
            "topological_entropy": ("topological_dynamics", "Dynamics.coverEntropy_restrict"),
            "circle_dynamics": ("topological_dynamics", "CircleDeg1Lift.translationNumber_eq_rat_iff"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "dynamical_systems", "analysis", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_dynamics_references_link_their_pinned_records(self):
        snapshot = open_snapshot(ROOT)
        references = snapshot.citations("discrete_gronwall")
        self.assertIn("Gronwall_1919", {entry["key"] for entry in references["module_citations"]})

    def test_ordinal_notation_correspondence_matches_reference_types(self):
        run(ROOT, [self.lake, "env", "lean", "tests/OrdinalNotationStatements.lean"], capture=True)

    def test_ordinal_notation_correspondence_retains_local_terms_and_source(self):
        names = [
            "Math.OrdinalNotation.repr_lt_epsilon_zero",
            "Math.OrdinalNotation.exists_normal_repr",
            "Math.OrdinalNotation.normal_repr_lt_epsilon_zero",
            "Math.OrdinalNotation.normal_repr_injective",
            "Math.OrdinalNotation.lt_epsilon_zero_iff",
            "Math.OrdinalNotation.normal_repr_bijective",
            "Math.OrdinalNotation.normal_order_iso",
            "Math.OrdinalNotation.normal_order_iso_apply",
            "Math.OrdinalNotation.repr_normal_order_iso_symm",
            "Math.OrdinalNotation.repr_ne_epsilon_zero",
            "Math.OrdinalNotation.normal_order_iso_add",
            "Math.OrdinalNotation.normal_order_iso_sub",
            "Math.OrdinalNotation.normal_order_iso_mul",
            "Math.OrdinalNotation.normal_order_iso_opow",
            "Math.OrdinalNotation.exists_unique_normal_form",
            "Math.OrdinalNotation.opow_lt_epsilon_zero",
        ]
        module = "Math.SetTheory.OrdinalNotation"
        origin = self.catalog["sources"][module]
        path = ROOT / "Math/SetTheory/OrdinalNotation.lean"
        self.assertEqual(origin["package"], "math")
        self.assertEqual(origin["path"], path.relative_to(ROOT).as_posix())
        self.assertEqual(origin["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        for name in names:
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], module)
                self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= set(self.policy["modules"][module]["allowed_axioms"]))
                self.assertGreater(node["source"]["line"], 0)

    def test_ordinal_notation_correspondence_reaches_both_models_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "Math.OrdinalNotation.repr_lt_epsilon_zero": {
                "ONote",
                "Ordinal.IsPrincipal",
                "Ordinal.veblen",
                "Ordinal.opow_mul_lt_opow",
            },
            "Math.OrdinalNotation.exists_normal_repr": {
                "Ordinal.log",
                "ONote.NF",
                "Ordinal.epsilon_zero_le_of_omega0_opow_le",
                "Ordinal.div_opow_log_lt",
            },
            "Math.OrdinalNotation.normal_order_iso": {
                "Math.OrdinalNotation.repr_lt_epsilon_zero",
                "Math.OrdinalNotation.exists_normal_repr",
                "Equiv.ofBijective",
                "NONote.repr",
            },
            "Math.OrdinalNotation.exists_unique_normal_form": {
                "Math.OrdinalNotation.normal_repr_injective",
                "Math.OrdinalNotation.repr_lt_epsilon_zero",
                "Math.OrdinalNotation.exists_normal_repr",
            },
            "Math.OrdinalNotation.opow_lt_epsilon_zero": {
                "NONote.opow",
                "NONote.repr_opow",
                "Math.OrdinalNotation.normal_repr_lt_epsilon_zero",
                "Math.OrdinalNotation.exists_normal_repr",
            },
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_ordinal_notation_correspondence_is_browsable_through_foundations(self):
        graph = KnowledgeGraph(self.catalog)
        name = "Math.OrdinalNotation.normal_order_iso"
        for subject in ("ordinal_notation", "ordinal_arithmetic", "ordinals", "set_theory",
                        "foundations", "mathematics"):
            with self.subTest(subject=subject):
                self.assertIn(name, {node["name"] for node in graph.search(name, subject=subject)})

    def test_probability_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "ProbabilityTheory.HasLaw": "Probability.HasLaw",
            "ProbabilityTheory.IdentDistrib": "Probability.IdentDistrib",
            "ProbabilityTheory.IndepFun": "Probability.Independence.Basic",
            "ProbabilityTheory.iIndepFun": "Probability.Independence.Basic",
            "ProbabilityTheory.iIndepSet": "Probability.Independence.Basic",
            "ProbabilityTheory.iCondIndepFun": "Probability.Independence.Conditional",
            "ProbabilityTheory.variance": "Probability.Moments.Variance",
            "ProbabilityTheory.covariance": "Probability.Moments.Covariance",
            "ProbabilityTheory.bernoulliMeasure": "Probability.Distributions.Bernoulli",
            "ProbabilityTheory.binomial": "Probability.Distributions.Binomial",
            "MeasureTheory.pdf.IsUniform": "Probability.Distributions.Uniform",
            "ProbabilityTheory.gaussianReal": "Probability.Distributions.Gaussian.Real",
            "ProbabilityTheory.poissonMeasure": "Probability.Distributions.Poisson.Basic",
            "MeasureTheory.condExp": "MeasureTheory.Function.ConditionalExpectation.Basic",
            "MeasureTheory.condExp_condExp_of_le": "MeasureTheory.Function.ConditionalExpectation.Basic",
            "MeasureTheory.TendstoInDistribution": "MeasureTheory.Function.ConvergenceInDistribution",
            "MeasureTheory.measure_limsup_atTop_eq_zero": "MeasureTheory.OuterMeasure.BorelCantelli",
            "ProbabilityTheory.measure_limsup_eq_one": "Probability.BorelCantelli",
            "ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop": "Probability.Independence.ZeroOne",
            "ProbabilityTheory.strong_law_ae": "Probability.StrongLaw",
            "ProbabilityTheory.strong_law_Lp": "Probability.StrongLaw",
            "ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub": "Probability.CentralLimitTheorem",
            "MeasureTheory.Filtration": "Probability.Process.Filtration",
            "MeasureTheory.StronglyAdapted": "Probability.Process.Adapted",
            "MeasureTheory.IsStoppingTime": "Probability.Process.Stopping",
            "MeasureTheory.stoppedValue": "Probability.Process.Stopping",
            "MeasureTheory.hittingAfter": "Probability.Process.HittingTime",
            "MeasureTheory.Filtration.limitProcess": "Probability.Process.LimitProcess",
            "MeasureTheory.Martingale": "Probability.Martingale.Basic",
            "MeasureTheory.Submartingale": "Probability.Martingale.Basic",
            "MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le": "Probability.Martingale.OptionalSampling",
            "MeasureTheory.Submartingale.expected_stoppedValue_mono": "Probability.Martingale.OptionalStopping",
            "MeasureTheory.Submartingale.ae_tendsto_limitProcess": "Probability.Martingale.Convergence",
            "MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess": "Probability.Martingale.Convergence",
            "MeasureTheory.Martingale.ae_eq_condExp_limitProcess": "Probability.Martingale.Convergence",
            "MeasureTheory.ae_mem_limsup_atTop_iff": "Probability.Martingale.BorelCantelli",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], "Mathlib." + suffix)
                if node["kind"] in {"definition", "theorem", "opaque"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][node["module"]]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_probability_hierarchies_reach_models_assumptions_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "ProbabilityTheory.strong_law_ae":
                {"ProbabilityTheory.IndepFun", "ProbabilityTheory.IdentDistrib", "MeasureTheory.Integrable",
                 "MeasureTheory.integral", "Filter.Tendsto"},
            "ProbabilityTheory.strong_law_Lp":
                {"MeasureTheory.MemLp", "MeasureTheory.eLpNorm", "ProbabilityTheory.IdentDistrib"},
            "ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub":
                {"ProbabilityTheory.HasLaw", "ProbabilityTheory.gaussianReal", "ProbabilityTheory.variance",
                 "ProbabilityTheory.iIndepFun", "MeasureTheory.MemLp", "MeasureTheory.TendstoInDistribution"},
            "ProbabilityTheory.measure_limsup_eq_one":
                {"ProbabilityTheory.iIndepSet", "MeasureTheory.Measure", "Filter.limsup"},
            "MeasureTheory.condExp_condExp_of_le":
                {"MeasureTheory.condExp", "MeasurableSpace", "MeasureTheory.SigmaFinite"},
            "MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le":
                {"MeasureTheory.Martingale", "MeasureTheory.Filtration", "MeasureTheory.IsStoppingTime",
                 "MeasureTheory.stoppedValue", "MeasureTheory.condExp"},
            "MeasureTheory.Submartingale.ae_tendsto_limitProcess":
                {"MeasureTheory.Submartingale", "MeasureTheory.eLpNorm", "MeasureTheory.Filtration.limitProcess"},
            "MeasureTheory.Martingale.ae_eq_condExp_limitProcess":
                {"MeasureTheory.Martingale", "MeasureTheory.UniformIntegrable", "MeasureTheory.condExp"},
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_probability_subjects_include_their_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "independence": ("probability", "ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop"),
            "probability_distributions": ("probability", "ProbabilityTheory.gaussianReal"),
            "probability_limits": ("probability", "ProbabilityTheory.strong_law_ae"),
            "stochastic_processes": ("probability", "MeasureTheory.IsStoppingTime"),
            "martingales": ("stochastic_processes", "MeasureTheory.Martingale.ae_eq_condExp_limitProcess"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "probability", "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_number_theory_hierarchies_reach_models_and_all_foundations(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "legendreSym.quadratic_reciprocity": {"legendreSym", "quadraticChar", "ZMod", "Nat.Prime"},
            "jacobiSym.quadratic_reciprocity": {"jacobiSym", "legendreSym", "Odd"},
            "Pell.exists_of_not_isSquare": {"Int", "IsSquare", "Real.sqrt", "Irrational"},
            "Pell.existsUnique_pos_generator": {"Pell.Solution₁", "Pell.IsFundamental", "Zsqrtd"},
            "Ideal.finprod_heightOneSpectrum_factorization":
                {"Ideal", "IsDedekindDomain", "IsDedekindDomain.HeightOneSpectrum",
                 "IsDedekindDomain.HeightOneSpectrum.maxPowDividing"},
            "NumberField.classNumber_eq_one_iff":
                {"NumberField", "NumberField.RingOfIntegers", "ClassGroup", "IsPrincipalIdealRing"},
            "NumberField.exists_ideal_in_class_of_norm_le":
                {"ClassGroup", "Ideal.absNorm", "NumberField.discr", "Real.sqrt", "NumberField.InfinitePlace"},
            "NumberField.Units.finrank_modTorsion":
                {"NumberField.Units.torsion", "NumberField.Units.rank", "NumberField.InfinitePlace", "Module.finrank"},
            "NumberField.Units.exist_unique_eq_mul_prod":
                {"NumberField.RingOfIntegers", "NumberField.Units.torsion", "NumberField.Units.fundSystem", "Module.Basis"},
            "NumberField.prod_abs_eq_one":
                {"NumberField.InfinitePlace", "NumberField.FinitePlace", "Algebra.norm", "NumberField.RingOfIntegers"},
            "NumberField.Ideal.primesOverSpanEquivMonicFactorsMod":
                {"RingOfIntegers.exponent", "minpoly", "Ideal.primesOver", "ZMod", "Nat.Prime"},
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_number_theory_subjects_include_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "modular_arithmetic": ("number_theory", "ZMod"),
            "quadratic_reciprocity": ("number_theory", "legendreSym.quadratic_reciprocity"),
            "diophantine_equations": ("number_theory", "Pell.existsUnique_pos_generator"),
            "algebraic_number_theory": ("number_theory", "NumberField.Units.exist_unique_eq_mul_prod"),
            "commutative_algebra": ("algebra", "ClassGroup"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_algebra_objects_and_results_retain_terms_and_pinned_sources(self):
        expected = {
            "Ring": "Algebra.Ring.Defs",
            "Field": "Algebra.Field.Defs",
            "Algebra": "Algebra.Algebra.Defs",
            "Polynomial": "Algebra.Polynomial.Basic",
            "MvPolynomial": "Algebra.MvPolynomial.Basic",
            "Ideal": "RingTheory.Ideal.Defs",
            "IsNoetherian": "RingTheory.Noetherian.Defs",
            "IsNoetherianRing": "RingTheory.Noetherian.Defs",
            "IntermediateField": "FieldTheory.IntermediateField.Basic",
            "minpoly": "FieldTheory.Minpoly.Basic",
            "Normal": "FieldTheory.Normal.Defs",
            "IsGalois": "FieldTheory.Galois.Basic",
            "IsAlgClosed": "FieldTheory.IsAlgClosed.Basic",
            "Polynomial.SplittingField": "FieldTheory.SplittingField.Construction",
            "Polynomial.Gal": "FieldTheory.PolynomialGaloisGroup",
            "Group.IsSolvable": "GroupTheory.Solvable",
            "PrimeSpectrum": "RingTheory.Spectrum.Prime.Defs",
            "IsGalois.intermediateFieldEquivSubgroup": "FieldTheory.Galois.Basic",
            "IsGalois.fixedField_fixingSubgroup": "FieldTheory.Galois.Basic",
            "IntermediateField.fixingSubgroup_fixedField": "FieldTheory.Galois.Basic",
            "Field.exists_primitive_element": "FieldTheory.PrimitiveElement",
            "IsGalois.normalBasis": "FieldTheory.Galois.NormalBasis",
            "IsGalois.normalBasis_apply": "FieldTheory.Galois.NormalBasis",
            "InfiniteGalois.IntermediateFieldEquivClosedSubgroup": "FieldTheory.Galois.Infinite",
            "InfiniteGalois.continuousMulEquivToLimit": "FieldTheory.Galois.Profinite",
            "solvableByRad": "FieldTheory.AbelRuffini",
            "isSolvable_gal_of_irreducible": "FieldTheory.AbelRuffini",
            "MvPolynomial.vanishingIdeal_zeroLocus_eq_radical": "RingTheory.Nullstellensatz",
            "MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton": "RingTheory.Nullstellensatz",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], "Mathlib." + suffix)
                if node["kind"] in {"theorem", "definition"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())
                origin = self.catalog["sources"][node["module"]]
                self.assertEqual(origin["revision"], self.policy["libraries"]["mathlib"]["revision"])
                self.assertIn(origin["revision"], origin["url"])
                self.assertEqual(origin["license"], "Apache-2.0")

    def test_algebra_hierarchies_reach_objects_hypotheses_and_all_axioms(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "IsGalois.intermediateFieldEquivSubgroup":
                {"IntermediateField", "Subgroup", "OrderDual", "IsGalois", "Module.Finite"},
            "InfiniteGalois.IntermediateFieldEquivClosedSubgroup":
                {"IntermediateField", "ClosedSubgroup", "TopologicalSpace", "IsGalois", "OrderDual"},
            "IsGalois.normalBasis": {"Module.Basis", "AlgEquiv", "IsGalois", "Module.Finite"},
            "InfiniteGalois.continuousMulEquivToLimit":
                {"ContinuousMulEquiv", "ProfiniteGrp.limit", "TopologicalSpace", "IsGalois"},
            "isSolvable_gal_of_irreducible":
                {"solvableByRad", "Group.IsSolvable", "Polynomial.Gal", "Irreducible"},
            "MvPolynomial.vanishingIdeal_zeroLocus_eq_radical":
                {"MvPolynomial", "Ideal", "Ideal.radical", "IsAlgClosed", "Finite",
                 "MvPolynomial.zeroLocus", "MvPolynomial.vanishingIdeal"},
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_algebra_subjects_include_their_results_and_parent_subjects(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "commutative_algebra": ("algebra", "IsNoetherianRing"),
            "field_theory": ("algebra", "IsGalois.intermediateFieldEquivSubgroup"),
            "algebraic_geometry": ("geometry", "MvPolynomial.vanishingIdeal_zeroLocus_eq_radical"),
            "group_theory": ("algebra", "Group.IsSolvable"),
        }
        for subject, (parent, name) in expected.items():
            with self.subTest(subject=subject):
                self.assertEqual(self.catalog["subjects"][subject]["parent"], parent)
                for category in (subject, parent, "mathematics"):
                    self.assertIn(name, {node["name"] for node in graph.search(name, subject=category)})

    def test_computability_models_and_results_retain_complete_terms(self):
        expected = {
            "Nat.Primrec": "Primrec.Basic",
            "Nat.Partrec": "Partrec",
            "Computable": "Partrec",
            "Nat.Partrec.Code": "PartrecCode",
            "Nat.Partrec.Code.eval_part": "PartrecCode",
            "Nat.Partrec.Code.fixed_point₂": "PartrecCode",
            "ComputablePred": "RE",
            "REPred": "RE",
            "ComputablePred.rice₂": "Halting",
            "ComputablePred.halting_problem": "Halting",
            "ComputablePred.halting_problem_re": "Halting",
            "ComputablePred.halting_problem_not_re": "Halting",
            "ack": "Ackermann",
            "not_primrec₂_ack": "Ackermann",
            "computable₂_ack": "Ackermann",
            "TuringDegree": "TuringDegree",
            "TuringEquivalent.equivalence": "TuringDegree",
            "Turing.Tape": "TuringMachine.Tape",
            "Turing.TM2.Stmt": "TuringMachine.StackTuringMachine",
            "Turing.PartrecToTM2.tr_eval": "TuringMachine.ToPartrec",
            "Turing.PartrecToTM2.tr_supports": "TuringMachine.ToPartrec",
            "Turing.FinTM2": "TuringMachine.Computable",
        }
        for name, suffix in expected.items():
            with self.subTest(name=name):
                self.assertIn(name, self.catalog["roots"])
                node = self.nodes[name]
                self.assertEqual(node["module"], "Mathlib.Computability." + suffix)
                if node["kind"] in {"theorem", "definition"}:
                    self.assertIsInstance(node["value"], int)
                self.assertTrue(set(node["axioms"]) <= self.policy["axioms"].keys())

    def test_computability_hierarchies_reach_models_and_foundations(self):
        graph = KnowledgeGraph(self.catalog)
        expected = {
            "ComputablePred.halting_problem":
                {"ComputablePred", "ComputablePred.rice", "Nat.Partrec.Code.eval", "Nat.Partrec"},
            "not_primrec₂_ack": {"ack", "Nat.Primrec", "Primrec₂"},
            "computable₂_ack": {"ack", "Computable₂", "Nat.Partrec.Code.eval", "Nat.Partrec"},
            "Turing.PartrecToTM2.tr_eval":
                {"Turing.TM2.step", "StateTransition.eval", "Turing.ToPartrec.Code.eval"},
        }
        for name, objects in expected.items():
            with self.subTest(name=name):
                hierarchy = graph.hierarchy(name)
                reached = {node["name"] for node in hierarchy["declarations"]}
                self.assertTrue(objects <= reached, objects - reached)
                self.assertEqual(set(hierarchy["axiom_paths"]), set(self.nodes[name]["axioms"]))
                for axiom, path in hierarchy["axiom_paths"].items():
                    self.assertEqual(path[0], name)
                    self.assertEqual(path[-1], axiom)
                    for source, target in zip(path, path[1:]):
                        self.assertIn(target, self.nodes[source]["dependencies"])

    def test_computation_subjects_expose_recursive_and_machine_results(self):
        graph = KnowledgeGraph(self.catalog)
        for subject, names in {
            "computation": {"ComputablePred.halting_problem", "Turing.PartrecToTM2.tr_eval", "TuringDegree"},
            "computability": {"ComputablePred.rice₂", "not_primrec₂_ack", "computable₂_ack"},
            "turing_machines": {"Turing.FinTM2", "Turing.PartrecToTM2.tr_supports"},
        }.items():
            with self.subTest(subject=subject):
                self.assertTrue(names <= {node["name"] for node in graph.search(subject=subject)})

    def test_new_fields_remain_accessible_through_subject_ancestors(self):
        graph = KnowledgeGraph(self.catalog)
        for subject, name in [("analysis", "Complex.exists_root"),
                              ("analysis", "intervalIntegral.integral_eq_sub_of_hasDerivAt"),
                              ("algebra", "Sylow.exists_subgroup_card_pow_prime"),
                              ("combinatorics", "SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph"),
                              ("foundations", "Function.Embedding.schroeder_bernstein")]:
            with self.subTest(subject=subject, name=name):
                self.assertIn(name, {node["name"] for node in graph.search(subject=subject)})

    def test_shared_generated_declarations_are_retained_from_serialized_modules(self):
        expected = {"LinearEquiv.restrictScalars.congr_simp", "LinearEquiv.ofEq.congr_simp",
                    "Finsupp.linearEquivFunOnFinite.congr_simp", "Function.comp_def._simp_1",
                    "MonoidWithZeroHom.mk.congr_simp", "Filter.Tendsto.eq_1"}
        self.assertTrue(expected <= set(self.catalog["roots"]))
        membership = self.catalog["module_declarations_by_module"]
        for name in expected:
            owners = {module for module, names in membership.items() if name in names}
            self.assertTrue(owners, name)
            if self.nodes[name]["module"] in self.catalog["module_policy"]:
                self.assertIn(self.nodes[name]["module"], owners)

    def test_serialized_module_inventory_cannot_be_omitted(self):
        raw = self.catalog.copy()
        raw.pop("module_declarations_by_module")
        with self.assertRaisesRegex(RepositoryError, "serialized module inventories"):
            validate(raw, self.policy)

    def test_shared_declarations_must_satisfy_every_selecting_module_budget(self):
        raw = {**self.catalog, "module_declarations_by_module": deepcopy(self.catalog["module_declarations_by_module"])}
        raw["module_declarations_by_module"]["Math.Logic.Basic"].append("Complex.exists_root")
        with self.assertRaisesRegex(RepositoryError, "module axiom budget exceeded in Math.Logic.Basic"):
            validate(raw, self.policy)

    def test_unsafe_programs_in_project_modules_are_rejected(self):
        self.assert_bad_contribution("unsafe def display_only : Nat := 0\n",
                                     "unsafe declarations are not allowed in project modules")

    def test_complete_inductive_axioms_are_retained_beyond_cached_summaries(self):
        node = self.nodes["T2Space"]
        self.assertEqual(set(node["axioms"]), {"Classical.choice", "propext", "Quot.sound"})
        self.assertTrue(set(node["lean_axioms"]) < set(node["axioms"]))
        self.assertGreater(self.catalog["axiom_audit"]["cached_summary_differences"], 0)

    def test_cached_axioms_cannot_exceed_the_fresh_dependency_closure(self):
        raw, node = self.mutated("Math.Logic.truth")
        node["lean_axioms"] = ["Classical.choice"]
        with self.assertRaisesRegex(RepositoryError, "cached Lean axioms missing from dependency graph"):
            validate(raw, self.policy)

    def test_safe_meta_annotations_preserve_checked_definitions_and_dependencies(self):
        node = self.nodes["Topology.delabContinuous"]
        self.assertTrue(node["meta"])
        self.assertFalse(node["unsafe"])
        self.assertFalse(node["partial"])
        self.assertIn("Topology.delabContinuous", self.catalog["roots"])
        self.assertTrue(self.nodes["CanLift"]["meta"])
        self.assertIn("Float", self.nodes)

    def test_query_store_preserves_the_entire_verified_corpus(self):
        snapshot = open_snapshot(ROOT)
        with snapshot.connect() as connection:
            self.assertEqual(connection.execute("SELECT count(*) FROM expressions").fetchone()[0], len(self.catalog["expressions"]))
            self.assertEqual(connection.execute("SELECT count(*) FROM declarations").fetchone()[0], len(self.nodes))
            for name, record, value in connection.execute("SELECT name, record, digest FROM declarations"):
                self.assertEqual(json.loads(record), self.nodes[name])
                self.assertEqual(value, self.catalog["declaration_hashes"][name])
        for name, node in self.nodes.items():
            actual = snapshot.graph.nodes[name]
            for field in ["dependencies", "type_dependencies", "value_dependencies", "structural_dependencies"]:
                self.assertEqual(set(actual[field]), set(node[field]), (name, field))

    def test_query_store_search_and_source_match_verified_mathematics(self):
        snapshot = open_snapshot(ROOT)
        results = snapshot.search("mean value", subject="analysis", kind="theorem")
        expected = KnowledgeGraph(self.catalog).search("mean value", subject="analysis", kind="theorem")
        self.assertEqual([item["name"] for item in results["items"]], [item["name"] for item in expected[:30]])
        source = snapshot.source("exists_hasDerivAt_eq_slope")
        self.assertIn("exists_hasDerivAt_eq_slope", "\n".join(source["lines"]))

    def test_query_store_streams_the_byte_identical_complete_catalog(self):
        snapshot = open_snapshot(ROOT)
        actual = hashlib.sha256()
        for chunk in snapshot.catalog_chunks():
            actual.update(chunk)
        self.assertEqual(actual.hexdigest(), snapshot.receipt["catalog_file_digest"])

    def test_every_indexed_logical_declaration_is_bound_to_both_checker_inputs(self):
        binding = self.catalog["proof_binding"]
        self.assertEqual(binding["indexed_declarations"], len(self.nodes))
        self.assertEqual(binding["matched_declarations"], len(self.nodes))
        self.assertEqual(binding["indexed_expressions"], len(self.catalog["expressions"]))
        self.assertEqual(binding["proof_export_digest"], self.catalog["provenance"]["proof_export_digest"])
        snapshot = open_snapshot(ROOT)
        self.assertEqual(snapshot.summary()["proof_binding"], binding)


class VerifiedCatalogLoadingTests(RepositoryArtifacts, unittest.TestCase):
    """load full catalogs after graph checks release their expression arrays."""

    @classmethod
    def setUpClass(cls):
        cls.catalog = open_snapshot(ROOT).metadata

    def test_source_changes_invalidate_index(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.clone_inputs(root)
            self.clone_artifact(root)
            self.assertEqual(load_catalog(root)["roots"], self.catalog["roots"])
            source = root / "Math/Logic/Basic.lean"
            source.write_text(source.read_text() + "\n")
            with self.assertRaisesRegex(RepositoryError, "index is stale"):
                load_catalog(root)

    def test_artifact_changes_are_detected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.clone_inputs(root)
            self.clone_artifact(root)
            raw = load_catalog(ROOT)
            raw["declarations"][0]["statement"] = "False"
            with (root / "build/knowledge.json").open("wb") as handle:
                for chunk in canonical_chunks(raw):
                    handle.write(chunk)
            del raw
            gc.collect()
            with self.assertRaisesRegex(RepositoryError, "content digest mismatch"):
                load_catalog(root)

    def test_proof_export_is_required_and_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.clone_inputs(root)
            self.clone_artifact(root)
            proof = next((root / "build").glob("proofs-*.jsonl"))
            with proof.open("ab") as handle:
                handle.write(b"tampered\n")
            with patch("repository.build.stream_digest", side_effect=AssertionError("catalog digest computed")):
                with self.assertRaisesRegex(RepositoryError, "proof export digest mismatch"):
                    load_catalog(root)
            proof.unlink()
            with patch("repository.build.stream_digest", side_effect=AssertionError("catalog digest computed")):
                with self.assertRaisesRegex(RepositoryError, "proof export is missing"):
                    load_catalog(root)


    def test_native_snapshot_is_bound_to_the_lean_verification(self):
        from repository.metamath_store import Snapshot
        snapshot = Snapshot(ROOT / "build/metamath")
        try:
            receipt = self.catalog["provenance"]["native_snapshots"]["metamath"]
            self.assertEqual(receipt["snapshot_digest"], snapshot.digest)
            self.assertEqual(snapshot.manifest["counts"]["Provable"], 71837)
            self.assertEqual(snapshot.manifest["counts"]["Axiom"], 4571)
            self.assertEqual(len(snapshot.manifest["databases"]), 9)
            self.assertEqual(snapshot.manifest["provenance"]["inputs"], input_hashes(ROOT))
            self.assertEqual(len(snapshot.manifest["provenance"]["checkers"]), 3)
        finally:
            snapshot.close()

    def test_native_sources_and_proof_steps_are_accessible(self):
        from repository.metamath_store import Snapshot
        snapshot = Snapshot(ROOT / "build/metamath")
        try:
            for name in ["metamath:set.mm:pm2.43", "metamath:iset.mm:id", "metamath:nf.mm:id",
                         "metamath:demo0.mm:th1"]:
                with self.subTest(name=name):
                    node = snapshot.declaration(name)
                    self.assertEqual(node["kind"], "Provable")
                    self.assertTrue(snapshot.source(name))
                    proof = snapshot.proof(name)
                    self.assertTrue(proof["tokens"])
                    self.assertTrue(proof["dag"]["nodes"])
                    for axiom in snapshot.assumptions(name)["axiom_rules"]:
                        path = snapshot.path(name, axiom)
                        self.assertEqual(path[0], name)
                        self.assertEqual(path[-1], axiom)
        finally:
            snapshot.close()

    def test_native_dependency_graph_preserves_every_axiom_closure(self):
        from collections import defaultdict
        from repository.metamath_store import Snapshot
        snapshot = Snapshot(ROOT / "build/metamath")
        try:
            for database in snapshot.manifest["databases"]:
                row = snapshot.connection.execute("select verification from databases where id=?", (database,)).fetchone()
                labels = json.loads(row[0])["axiom_labels"]
                indices = {label: index for index, label in enumerate(labels)}
                edges = defaultdict(list)
                for source, target in snapshot.connection.execute(
                    "select d.declaration_id,d.dependency_id from dependencies d "
                    "join declarations n on n.id=d.declaration_id where n.database_id=?", (database,)):
                    edges[source].append(target)
                known = {}
                for node in snapshot.connection.execute("select * from declarations where database_id=? order by ordinal", (database,)):
                    bits = 0
                    for child in edges[node["id"]]:
                        self.assertIn(child, known)
                        self.assertTrue(child.startswith("metamath:" + database + ":"))
                        bits |= known[child]
                    if node["kind"] == "Axiom":
                        bits = 1 << indices[node["label"]]
                    if node["checked"]:
                        self.assertEqual(int(json.loads(node["checked"])["axiom_bits"], 16), bits)
                    known[node["id"]] = bits
        finally:
            snapshot.close()

    def test_native_source_primitives_retain_every_symbol_scope_and_frame_condition(self):
        from repository.metamath_store import Snapshot
        snapshot = Snapshot(ROOT / 'build/metamath')
        try:
            symbols, clauses, scopes = {}, {}, {}
            for row in snapshot.connection.execute("select identifier,kind,record from primitive_objects"):
                record = json.loads(row['record'])
                if row['kind'] in ['constant', 'variable']:
                    symbols[row['identifier']] = record
                elif row['kind'] == 'disjoint':
                    clauses[row['identifier']] = record
                elif row['kind'] == 'scope':
                    scopes[row['identifier']] = record
            self.assertEqual((len(symbols), len(clauses), len(scopes)), (2812, 106779, 38444))
            named = occurrences = 0
            for row in snapshot.connection.execute('''select d.*,p.record from declarations d
                    left join primitive_objects p on p.declaration_id=d.id'''):
                self.assertIsNotNone(row['record'], row['id'])
                record = json.loads(row['record'])
                self.assertEqual(record['id'], row['id'])
                self.assertEqual(record['ordinal'], row['ordinal'])
                self.assertEqual(record['native_kind'], row['kind'])
                self.assertEqual(record['source'], {'start': row['source_start'], 'end': row['source_end'],
                                                   'line': row['source_line'], 'end_line': row['source_end_line']})
                self.assertEqual([symbols[name]['token'] for name in record['tokens']], json.loads(row['expression']))
                frame = json.loads(row['frame']) if row['frame'] else None
                for field, native in [('frame_variables', 'variables'), ('mandatory_variables', 'mandatory_variables')]:
                    self.assertEqual([symbols[name]['token'] for name in record[field]], frame[native] if frame else [])
                self.assertEqual(record['hypotheses'],
                                 ['metamath:' + row['database_id'] + ':' + label for label in frame['hypotheses']]
                                 if frame else [])
                ancestors, scope = set(), record['scope']
                while scope is not None:
                    self.assertNotIn(scope, ancestors)
                    ancestors.add(scope)
                    context = scopes[scope]
                    if context['ordinal'] is not None:
                        self.assertLess(context['ordinal'], row['ordinal'])
                        self.assertLess(row['ordinal'], context['close_ordinal'])
                    scope = context['parent']
                for symbol in set(record['tokens'] + record['frame_variables']):
                    self.assertIn(symbols[symbol]['scope'], ancestors)
                    self.assertLess(symbols[symbol]['ordinal'], row['ordinal'])
                for field in ['mandatory_disjoint', 'proof_disjoint']:
                    self.assertEqual([[symbols[name]['token'] for name in item['variables']] for item in record[field]],
                                     frame[field] if frame else [])
                    for item in record[field]:
                        clause = clauses[item['clause']]
                        self.assertTrue(set(item['variables']) <= set(clause['variables']))
                        self.assertIn(clause['scope'], ancestors)
                        self.assertLess(clause['ordinal'], row['ordinal'])
                named += 1
                occurrences += len(record['tokens'])
            self.assertEqual((named, occurrences), (164960, 2969703))
            mismatch = snapshot.connection.execute('''select count(*) from primitive_objects p,
                json_each(p.record,'$.tokens') token left join primitive_edges e
                on e.source_id=p.id and e.relation='expression_symbol' and e.position=token.key
                left join primitive_objects symbol on symbol.id=e.target_id
                where p.kind='assertion_symbols' and (symbol.id is null or symbol.identifier!=token.value)''').fetchone()[0]
            self.assertEqual(mismatch, 0)
            self.assertEqual(snapshot.connection.execute(
                "select count(*) from primitive_edges where relation='expression_symbol'").fetchone()[0], occurrences)
        finally:
            snapshot.close()

    def test_native_inputs_include_exporter_lock_and_source_fixtures(self):
        inputs = input_hashes(ROOT)
        for relative in ["metamath-lock.json", "tools/metamath-export/Cargo.toml",
                         "tools/metamath-export/Cargo.lock", "tools/metamath-export/src/main.rs",
                         "tests/fixtures/metamath/valid-saved_subproof.mm",
                         "tests/fixtures/metamath/valid-saved_subproof.jsonl"]:
            self.assertEqual(inputs[relative], hashlib.sha256((ROOT / relative).read_bytes()).hexdigest())

    def test_native_verifiers_reject_incomplete_and_invalid_proofs(self):
        import re
        import subprocess
        c = ROOT / ".tools/metamath/metamath"
        rust = ROOT / ".tools/metamath/knife-target/release/metamath-knife"
        for source in sorted((ROOT / "tests/fixtures/metamath").glob("negative-*.mm")):
            with self.subTest(source=source.name):
                checked = subprocess.run([str(c), f'read "{source}"', "verify proof *", "exit"],
                                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
                output = checked.stdout + checked.stderr
                self.assertFalse(checked.returncode == 0 and "All proofs in the database were verified in " in output
                                 and not any(line.lstrip().startswith("?") for line in output.splitlines()))
                checked = subprocess.run([str(rust), "--time", "--jobs", "2", "--split", "--verify", str(source)],
                                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
                output = re.sub(r"\x1b\[[0-9;]*m", "", checked.stdout + checked.stderr)
                self.assertFalse(checked.returncode == 0 and "0 diagnostics issued." in output)


if __name__ == "__main__":
    unittest.main()
