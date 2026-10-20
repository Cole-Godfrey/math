module

public import Mathlib.SetTheory.Ordinal.Notation
public import Mathlib.SetTheory.Ordinal.Veblen

set_option autoImplicit false
set_option warningAsError true

open Ordinal
open scoped Ordinal

/-!
normal finite ordinal notations correspond exactly to ordinals below epsilon zero.
the correspondence preserves order and the implemented arithmetic operations.
-/

@[expose] public section

namespace Math.OrdinalNotation

/-- every finite notation denotes an ordinal below epsilon zero. -/
theorem repr_lt_epsilon_zero (o : ONote) : o.repr < ε₀ := by
  have hadd : IsPrincipal (· + ·) (ε₀ : Ordinal.{0}) := by
    simpa only [omega0_opow_epsilon] using isPrincipal_add_omega0_opow (ε₀ : Ordinal.{0})
  induction o with
  | zero => exact epsilon_pos 0
  | oadd e n a he ha =>
    change ω ^ e.repr * (n : Ordinal) + a.repr < ε₀
    apply hadd (by
      simpa only [omega0_opow_epsilon] using
        opow_mul_lt_opow (natCast_lt_omega0 (n : ℕ)) he) ha

/-- every ordinal below epsilon zero has a normal finite notation. -/
theorem exists_normal_repr : ∀ o : Ordinal.{0}, o < ε₀ → ∃ a : ONote, a.NF ∧ a.repr = o := by
  intro o
  refine Ordinal.lt_wf.induction (motive := fun o : Ordinal.{0} => o < ε₀ → ∃ a : ONote, a.NF ∧ a.repr = o) o ?_
  intro o ih ho
  by_cases hz : o = 0
  · subst o
    exact ⟨0, ONote.NF.zero, rfl⟩
  let e := log ω o
  let r := o % ω ^ e
  have he_lt : e < o := by
    refine lt_of_le_of_ne (log_le_self ω o) ?_
    intro heq
    have hfixed : ω ^ o ≤ o := by
      simpa only [show log ω o = o from heq] using opow_log_le_self ω hz
    exact (not_le_of_gt ho) (epsilon_zero_le_of_omega0_opow_le hfixed)
  have hr_lt : r < o := mod_opow_log_lt_self ω hz
  obtain ⟨ae, hae, he⟩ := ih e he_lt (he_lt.trans ho)
  obtain ⟨ar, har, hr⟩ := ih r hr_lt (hr_lt.trans ho)
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt o one_lt_omega0)
  have hn_pos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hpos := div_opow_log_pos ω hz
    simp only [hn, hzero, Nat.cast_zero, lt_self_iff_false] at hpos
  have hbelow : ONote.NFBelow ar ae.repr := by
    apply ONote.NF.below_of_lt' _ har
    simpa only [he, hr] using mod_lt o (opow_ne_zero e omega0_ne_zero)
  refine ⟨ONote.oadd ae ⟨n, hn_pos⟩ ar, ONote.NF.oadd hae _ hbelow, ?_⟩
  change ω ^ ae.repr * (n : Ordinal) + ar.repr = o
  rw [he, hr, ← hn]
  exact div_add_mod o (ω ^ e)

/-- normal notations denote ordinals below epsilon zero. -/
theorem normal_repr_lt_epsilon_zero (o : NONote) : o.repr < ε₀ :=
  repr_lt_epsilon_zero o.1

/-- normal notations with the same ordinal interpretation are equal. -/
theorem normal_repr_injective : Function.Injective NONote.repr := by
  intro a b h
  apply Subtype.ext
  exact ONote.repr_inj.mp h

/-- bounded ordinals are exactly the interpretations of normal notations. -/
theorem lt_epsilon_zero_iff {o : Ordinal.{0}} :
    o < ε₀ ↔ ∃ a : NONote, a.repr = o := by
  constructor
  · intro ho
    obtain ⟨a, ha, he⟩ := exists_normal_repr o ho
    exact ⟨⟨a, ha⟩, he⟩
  · rintro ⟨a, rfl⟩
    exact normal_repr_lt_epsilon_zero a

/-- interpretation bijects normal notations with bounded ordinals. -/
theorem normal_repr_bijective :
    Function.Bijective (fun a : NONote =>
      (⟨a.repr, normal_repr_lt_epsilon_zero a⟩ : Set.Iio (ε₀ : Ordinal.{0}))) := by
  constructor
  · intro a b h
    exact normal_repr_injective (congrArg Subtype.val h)
  · rintro ⟨o, ho⟩
    obtain ⟨a, ha⟩ := lt_epsilon_zero_iff.mp ho
    exact ⟨a, Subtype.ext ha⟩

/-- normal ordinal notations have exactly the order below epsilon zero. -/
noncomputable def normal_order_iso : NONote ≃o Set.Iio (ε₀ : Ordinal.{0}) :=
  { Equiv.ofBijective (fun a : NONote =>
      (⟨a.repr, normal_repr_lt_epsilon_zero a⟩ : Set.Iio (ε₀ : Ordinal.{0})))
      normal_repr_bijective with
    map_rel_iff' := Iff.rfl }

@[simp]
theorem normal_order_iso_apply (a : NONote) : (normal_order_iso a).1 = a.repr := rfl

@[simp]
theorem repr_normal_order_iso_symm (o : Set.Iio (ε₀ : Ordinal.{0})) :
    (normal_order_iso.symm o).repr = o.1 :=
  congrArg Subtype.val (normal_order_iso.apply_symm_apply o)

/-- no finite ordinal notation represents epsilon zero. -/
theorem repr_ne_epsilon_zero (a : ONote) : a.repr ≠ ε₀ :=
  (repr_lt_epsilon_zero a).ne

/-- normal notation addition agrees with bounded ordinal addition. -/
theorem normal_order_iso_add (a b : NONote) :
    (normal_order_iso (a + b)).1 = (normal_order_iso a).1 + (normal_order_iso b).1 :=
  NONote.repr_add a b

/-- normal notation subtraction agrees with bounded ordinal subtraction. -/
theorem normal_order_iso_sub (a b : NONote) :
    (normal_order_iso (a - b)).1 = (normal_order_iso a).1 - (normal_order_iso b).1 :=
  NONote.repr_sub a b

/-- normal notation multiplication agrees with bounded ordinal multiplication. -/
theorem normal_order_iso_mul (a b : NONote) :
    (normal_order_iso (a * b)).1 = (normal_order_iso a).1 * (normal_order_iso b).1 :=
  NONote.repr_mul a b

/-- normal notation exponentiation agrees with bounded ordinal exponentiation. -/
theorem normal_order_iso_opow (a b : NONote) :
    (normal_order_iso (NONote.opow a b)).1 = (normal_order_iso a).1 ^ (normal_order_iso b).1 :=
  NONote.repr_opow a b

/-- each finite notation has a unique normal representative. -/
theorem exists_unique_normal_form (a : ONote) : ∃! n : NONote, n.repr = a.repr := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero_iff.mp (repr_lt_epsilon_zero a)
  exact ⟨n, hn, fun m hm => normal_repr_injective (hm.trans hn.symm)⟩

/-- exponentiation stays below epsilon zero when both operands do. -/
theorem opow_lt_epsilon_zero {a b : Ordinal.{0}} (ha : a < ε₀) (hb : b < ε₀) :
    a ^ b < ε₀ := by
  obtain ⟨na, rfl⟩ := lt_epsilon_zero_iff.mp ha
  obtain ⟨nb, rfl⟩ := lt_epsilon_zero_iff.mp hb
  simpa only [NONote.repr_opow] using normal_repr_lt_epsilon_zero (NONote.opow na nb)

end Math.OrdinalNotation
