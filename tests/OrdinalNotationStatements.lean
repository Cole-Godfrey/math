module

import Math.SetTheory.OrdinalNotation

open Ordinal Math.OrdinalNotation
open scoped Ordinal

noncomputable section

example (a : ONote) : a.repr < ε₀ := repr_lt_epsilon_zero a

example (o : Ordinal.{0}) (h : o < ε₀) : ∃ a : ONote, a.NF ∧ a.repr = o :=
  exists_normal_repr o h

example : NONote ≃o Set.Iio (ε₀ : Ordinal.{0}) := normal_order_iso

example (o : Ordinal.{0}) : o < ε₀ ↔ ∃ a : NONote, a.repr = o := lt_epsilon_zero_iff

example (a : ONote) : ∃! n : NONote, n.repr = a.repr := exists_unique_normal_form a

example (a : ONote) : a.repr ≠ ε₀ := repr_ne_epsilon_zero a

example (o : Set.Iio (ε₀ : Ordinal.{0})) : (normal_order_iso.symm o).repr = o.1 :=
  repr_normal_order_iso_symm o

example (a b : NONote) : normal_order_iso a ≤ normal_order_iso b ↔ a ≤ b :=
  normal_order_iso.le_iff_le

example (a b : NONote) :
    (normal_order_iso (a + b)).1 = (normal_order_iso a).1 + (normal_order_iso b).1 :=
  normal_order_iso_add a b

example (a b : NONote) :
    (normal_order_iso (a - b)).1 = (normal_order_iso a).1 - (normal_order_iso b).1 :=
  normal_order_iso_sub a b

example (a b : NONote) :
    (normal_order_iso (a * b)).1 = (normal_order_iso a).1 * (normal_order_iso b).1 :=
  normal_order_iso_mul a b

example (a b : NONote) :
    (normal_order_iso (NONote.opow a b)).1 = (normal_order_iso a).1 ^ (normal_order_iso b).1 :=
  normal_order_iso_opow a b

example {a b : Ordinal.{0}} (ha : a < ε₀) (hb : b < ε₀) : a ^ b < ε₀ :=
  opow_lt_epsilon_zero ha hb
