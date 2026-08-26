import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential

open Complex

def kuramoto_order (N : Nat) (phases : Nat → Real) : Complex :=
  (1 / (N : Real)) * ∑ i ∈ Finset.range N, exp (I * phases i)
