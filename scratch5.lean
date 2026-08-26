import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

example (x : Real) : |x - x| = 0 := by
  simp
