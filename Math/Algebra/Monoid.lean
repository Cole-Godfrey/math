import Math.Numbers.Natural

namespace Math.Algebra

universe u

/-- a monoid has an associative product and a two-sided identity. -/
structure Monoid (α : Type u) where
  one : α
  mul : α → α → α
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a

/-- a group is a monoid with a two-sided inverse for each element. -/
structure Group (α : Type u) extends Monoid α where
  inv : α → α
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

/-- a left identity in a monoid equals its identity. -/
theorem identity_unique {α : Type u} (m : Monoid α) (e : α)
    (h : ∀ a, m.mul e a = a) : e = m.one :=
  (m.mul_one e).symm.trans (h m.one)

/-- a left inverse and a right inverse of the same element are equal. -/
theorem inverse_unique {α : Type u} (m : Monoid α) {a b c : α}
    (hba : m.mul b a = m.one) (hac : m.mul a c = m.one) : b = c := by
  calc
    b = m.mul b m.one := (m.mul_one b).symm
    _ = m.mul b (m.mul a c) := congrArg (m.mul b) hac.symm
    _ = m.mul (m.mul b a) c := (m.assoc b a c).symm
    _ = m.mul m.one c := congrArg (fun x => m.mul x c) hba
    _ = c := m.one_mul c

/-- addition with zero gives a monoid on natural numbers. -/
def natural_addition : Monoid Nat where
  one := 0
  mul := Nat.add
  assoc := Math.Natural.add_assoc
  one_mul := Math.Natural.zero_add
  mul_one := Math.Natural.add_zero

/-- multiplication with one gives a monoid on natural numbers. -/
def natural_multiplication : Monoid Nat where
  one := 1
  mul := Nat.mul
  assoc := Math.Natural.mul_assoc
  one_mul := Math.Natural.one_mul
  mul_one := Math.Natural.mul_one

end Math.Algebra
