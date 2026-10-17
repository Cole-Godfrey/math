namespace Math.Natural

/-- induction proves a predicate on all natural numbers. -/
theorem induction {p : Nat → Prop} (base : p 0)
    (step : ∀ n, p n → p (Nat.succ n)) : ∀ n, p n :=
  fun n => Nat.rec base step n

/-- zero is a right identity for addition. -/
theorem add_zero (n : Nat) : n + 0 = n := rfl

/-- addition recurses on the second argument. -/
theorem add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := rfl

/-- zero is a left identity for addition. -/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/-- adding to a successor yields a successor. -/
theorem succ_add (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/-- natural number addition is associative. -/
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih => exact congrArg Nat.succ ih

/-- natural number addition is commutative. -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction b with
  | zero => exact (zero_add a).symm
  | succ b ih => exact (congrArg Nat.succ ih).trans (succ_add b a).symm

/-- multiplication by zero on the right is zero. -/
theorem mul_zero (n : Nat) : n * 0 = 0 := rfl

/-- multiplication recurses on the second argument. -/
theorem mul_succ (m n : Nat) : m * Nat.succ n = m * n + m := rfl

/-- multiplication by zero on the left is zero. -/
theorem zero_mul (n : Nat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- one is a right identity for multiplication. -/
theorem mul_one (n : Nat) : n * 1 = n := zero_add n

/-- multiplication distributes over addition in its second argument. -/
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rfl
  | succ c ih => exact (congrArg (fun n => n + a) ih).trans (add_assoc _ _ _)

/-- multiplication distributes over addition in its first argument. -/
theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    calc
      (a + b) * Nat.succ c = (a * c + b * c) + (a + b) :=
        congrArg (fun n => n + (a + b)) ih
      _ = a * c + (b * c + (a + b)) := add_assoc _ _ _
      _ = a * c + ((b * c + a) + b) := congrArg (fun n => a * c + n) (add_assoc _ _ _).symm
      _ = a * c + ((a + b * c) + b) :=
        congrArg (fun n => a * c + (n + b)) (add_comm (b * c) a)
      _ = a * c + (a + (b * c + b)) := congrArg (fun n => a * c + n) (add_assoc _ _ _)
      _ = (a * c + a) + (b * c + b) := (add_assoc _ _ _).symm

/-- one is a left identity for multiplication. -/
theorem one_mul (n : Nat) : 1 * n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/-- multiplication by a successor expands as an addition. -/
theorem succ_mul (a b : Nat) : Nat.succ a * b = a * b + b := by
  exact (add_mul a 1 b).trans (congrArg (fun n => a * b + n) (one_mul b))

/-- natural number multiplication is commutative. -/
theorem mul_comm (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => exact (zero_mul a).symm
  | succ b ih => exact (congrArg (fun n => n + a) ih).trans (succ_mul b a).symm

/-- natural number multiplication is associative. -/
theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => exact (congrArg (fun n => n + a * b) ih).trans (mul_add a (b * c) b).symm

/-- divisibility means being a natural number multiple. -/
def Divides (a b : Nat) : Prop := ∃ k, b = a * k

/-- every natural number divides itself. -/
theorem divides_refl (n : Nat) : Divides n n := ⟨1, (mul_one n).symm⟩

/-- divisibility is transitive. -/
theorem divides_trans {a b c : Nat} (hab : Divides a b) (hbc : Divides b c) :
    Divides a c := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  exact ⟨m * n, hn.trans ((congrArg (fun x => x * n) hm).trans (mul_assoc a m n))⟩

/-- an even natural number is a sum of two equal natural numbers. -/
def Even (n : Nat) : Prop := ∃ k, n = k + k

/-- the sum of even natural numbers is even. -/
theorem even_add {m n : Nat} (hm : Even m) (hn : Even n) : Even (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  refine ⟨a + b, ?_⟩
  rw [ha, hb]
  calc
    (a + a) + (b + b) = a + ((a + b) + b) :=
      (add_assoc a a (b + b)).trans (congrArg (fun x => a + x) (add_assoc a b b).symm)
    _ = a + ((b + a) + b) := congrArg (fun x => a + (x + b)) (add_comm a b)
    _ = a + (b + (a + b)) := congrArg (fun x => a + x) (add_assoc b a b)
    _ = (a + b) + (a + b) := (add_assoc a b (a + b)).symm

end Math.Natural
