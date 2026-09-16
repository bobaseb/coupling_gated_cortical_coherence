import Lean

namespace CompanionFixture

theorem identity {α : Type} (a : α) : a = a := rfl

theorem branched (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

structure Calibration where
  actual : Nat
  cap : Nat
  bounded : actual ≤ cap

theorem assumed_bound (c : Calibration) : c.actual ≤ c.cap := c.bounded

example (n : Nat) : n = n := by rfl

end CompanionFixture
