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
        raw, node = self.mutated("Nat.rec")
        node["structure"]["rules"][0]["rhs"] = {"tag": "mvar", "name": "unresolved"}
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
            "theorem admitted : False := by sorry\n", "undeclared foundational axiom")

    def test_axiom_outside_project_namespace_is_detected(self):
        self.assert_bad_contribution(
            "axiom hidden : False\ntheorem derived : False := hidden\n",
            "undeclared foundational axiom")

    def test_classical_axiom_budget_is_enforced(self):
        self.assert_bad_contribution(
            "theorem classical_result (P : Prop) : P ∨ ¬ P := Classical.em P\n",
            "module axiom budget exceeded")

    def test_compiler_based_proof_is_rejected(self):
        self.assert_bad_contribution(
            "import Lean\ntheorem native_result : (List.range 10).length = 10 := by native_decide\n",
            "undeclared foundational axiom")

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
            with self.assertRaisesRegex(RepositoryError, "proof export digest mismatch"):
                load_catalog(root)
            proof.unlink()
            with self.assertRaisesRegex(RepositoryError, "proof export is missing"):
                load_catalog(root)


if __name__ == "__main__":
    unittest.main()
