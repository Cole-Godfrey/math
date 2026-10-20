import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Descriptive.Tree
import Mathlib.SetTheory.Lists
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Class
import Mathlib.SetTheory.ZFC.VonNeumann

open Set Ordinal
open scoped Cardinal Ordinal ZFSet ZFClass

noncomputable section

universe u v

example {α : Type u} {r : α → α → Prop} {a b : α} (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h

section ZFCSets

variable {x y : ZFSet.{u}}

example (h : ∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) : x = y := ZFSet.ext h

example (x a b : ZFSet.{u}) : x ∈ ({a, b} : ZFSet) ↔ x = a ∨ x = b :=
  ZFSet.mem_pair

example (p : ZFSet.{u} → Prop) : y ∈ ZFSet.sep p x ↔ y ∈ x ∧ p y :=
  ZFSet.mem_sep

example : y ∈ (⋃₀ x : ZFSet.{u}) ↔ ∃ z ∈ x, y ∈ z := ZFSet.mem_sUnion

example : y ∈ ZFSet.powerset x ↔ y ⊆ x := ZFSet.mem_powerset

example : (∅ : ZFSet.{u}) ∈ ZFSet.omega := ZFSet.omega_zero

example (h : x ∈ ZFSet.omega) : insert x x ∈ ZFSet.omega := ZFSet.omega_succ h

example (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ := ZFSet.regularity x h

example (f : ZFSet.{u} → ZFSet.{u}) [ZFSet.Definable₁ f] :
    y ∈ ZFSet.image f x ↔ ∃ z ∈ x, f z = y :=
  ZFSet.mem_image

example (x : ZFSet.{u}) (h : ∅ ∉ x) :
    ZFSet.IsFunc x (⋃₀ x) (ZFSet.choice x) :=
  ZFSet.choice_isFunc x h

example (x : ZFSet.{u}) (h : ∅ ∉ x) (y : ZFSet.{u}) (hy : y ∈ x) :
    ZFSet.choice x ′ y ᶜ∈ (y : ZFClass.{u}) :=
  ZFSet.choice_cmem x h y hy

example : {x : ZFSet.{u} | ZFSet.IsOrdinal x} ᶜ∉ (.univ : ZFClass.{u}) :=
  ZFSet.isOrdinal_notCMem_univ

example : Ordinal.{u} ≃o {x : ZFSet.{u} // ZFSet.IsOrdinal x} := Ordinal.toZFSetIso

example (o : Ordinal.{u}) : o.toZFSet.rank = o := Ordinal.rank_toZFSet o

example (h : y ∈ x) : y.rank < x.rank := ZFSet.rank_lt_of_mem h

example (x : ZFSet.{u}) : (ZFSet.powerset x).card = 2 ^ x.card := ZFSet.card_powerset x

example (o : Ordinal.{u}) : x ∈ V_ o ↔ x.rank < o := ZFSet.mem_vonNeumann

example (o : Ordinal.{u}) : V_ (o + 1) = ZFSet.powerset (V_ o) :=
  ZFSet.vonNeumann_add_one o

example (x : ZFSet.{u}) : ∃ o : Ordinal.{u}, x ∈ V_ o := ZFSet.exists_mem_vonNeumann x

example (o : Ordinal.{u}) : (V_ o).card = Cardinal.preBeth o := ZFSet.card_vonNeumann o

end ZFCSets

section OrdinalArithmetic

example (b o : Ordinal.{u}) :
    (CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o :=
  CNF.foldr b o

example (o : Ordinal.{u}) : veblen 0 o = ω ^ o := veblen_zero_apply o

example (o : Ordinal.{u}) : ω ^ ε_ o = ε_ o := omega0_opow_epsilon o

example {o : Ordinal.{u}} (h : ω ^ o ≤ o) : ε₀ ≤ o :=
  epsilon_zero_le_of_omega0_opow_le h

example (o : Ordinal.{u}) :
    ∃ f : Iio o.cof.ord → Iio o, IsFundamentalSeq f :=
  exists_isFundamentalSeq rfl

example (a b : ONote) [ONote.NF a] [ONote.NF b] :
    ONote.repr (a + b) = ONote.repr a + ONote.repr b := ONote.repr_add a b

example (a b : ONote) [ONote.NF a] [ONote.NF b] :
    ONote.repr (a * b) = ONote.repr a * ONote.repr b := ONote.repr_mul a b

example (a b : ONote) [ONote.NF a] [ONote.NF b] :
    ONote.repr (a ^ b) = ONote.repr a ^ ONote.repr b := ONote.repr_opow a b

end OrdinalArithmetic

section CardinalArithmetic

example (κ : Cardinal.{u}) : κ < 2 ^ κ := Cardinal.cantor κ

example {κ : Cardinal.{u}} (h : ℵ₀ ≤ κ) : κ + κ = κ := Cardinal.add_eq_self h

example {κ : Cardinal.{u}} (h : ℵ₀ ≤ κ) : κ * κ = κ := Cardinal.mul_eq_self h

example (o : Ordinal.{u}) : Cardinal.IsRegular (ℵ_ (o + 1)) :=
  Cardinal.isRegular_aleph_add_one o

example : (ℶ_ 1 : Cardinal.{u}) = 𝔠 := Cardinal.beth_one

end CardinalArithmetic

section StationarySets

variable {α : Type v} [LinearOrder α] [WellFoundedLT α] [IsRegularCardinalOrder α]

example {s : Set α} {f : α → α} (hα : Order.cof α ≠ ℵ₀) (hs : IsStationary s)
    (hf : ∀ x ∈ s, f x < x) : ∃ a, IsStationary (s ∩ f ⁻¹' {a}) :=
  exists_isStationary_preimage_singleton hα hs hf

end StationarySets

section Trees

variable {α : Type u} {T : Descriptive.tree α}

example : CompleteLattice (Descriptive.tree α) := inferInstance

example {x y : List α} (hxy : x <+: y) (hy : y ∈ T) : x ∈ T :=
  Descriptive.Tree.mem_of_prefix hxy hy

example (S T : Descriptive.tree α) (x : List α) :
    Descriptive.Tree.pullSub S x ≤ T ↔ S ≤ Descriptive.Tree.subAt T x :=
  Descriptive.Tree.pullSub_adjunction S T x

end Trees
