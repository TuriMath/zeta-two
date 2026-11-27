import Mathlib

/-!
# ZetaTwo, statement A (Noether)

Source (TuriMath/zeta-two#1, quoted exactly):
> The sum of the reciprocals of the squares of the positive integers is π²/6:
> 1 + 1/4 + 1/9 + 1/16 + ⋯ = π²/6.
-/

namespace TuriMath.ZetaTwo.A

/-- The summand: the reciprocal of the square of the positive integer `n`, as a real number. -/
noncomputable def term (n : ℕ+) : ℝ := 1 / ((n : ℕ) : ℝ) ^ 2

/-- Euler's ζ(2) = π²/6 (the Basel problem).

Mapping from the source quote to the Lean:
* "the positive integers"            ↦ index type `ℕ+` (n = 1, 2, 3, …; no n = 0 term, so no `1/0 = 0` junk value).
* "the reciprocals of the squares"   ↦ `term n = 1 / (n : ℝ) ^ 2`, computed in `ℝ` (real division, not ℕ or ℚ).
* "the sum … is" / "1 + 1/4 + ⋯ ="   ↦ `HasSum`, Mathlib's infinite sum: the series converges and its value is the target.
  All terms are ≥ 0, so unconditional summation (`HasSum`) is the same as convergence of the
  partial sums 1 + 1/4 + ⋯ + 1/N in the order written; no stronger or weaker claim.
* "π²/6"                             ↦ `Real.pi ^ 2 / 6`, a real number.
-/
def Statement : Prop :=
  HasSum term (Real.pi ^ 2 / 6)

/-! ## Sanity section

`Statement` has no hypotheses, so there is nothing to show jointly satisfiable.
Instead we check that the summand matches the source's listed terms 1, 1/4, 1/9, 1/16. -/

example : term 1 = 1 := by norm_num [term]
example : term 2 = 1 / 4 := by norm_num [term]
example : term 3 = 1 / 9 := by norm_num [term]
example : term 4 = 1 / 16 := by norm_num [term]

end TuriMath.ZetaTwo.A
