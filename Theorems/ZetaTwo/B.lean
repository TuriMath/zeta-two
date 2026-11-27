import Mathlib

/-!
# ZetaTwo, statement B (Gauss, blind formalization)

Source (issue TuriMath/zeta-two#1, quoted exactly):
> The sum of the reciprocals of the squares of the positive integers is π²/6:
> 1 + 1/4 + 1/9 + 1/16 + ⋯ = π²/6.

Phrasing chosen: the most elementary one, an ε–N limit of the partial sums
`1 + 1/4 + ⋯ + 1/n²`, with no `HasSum`, `tsum` or filters.

Mapping, source → Lean:
* "the positive integers"                 → `k ∈ Finset.Icc 1 n`, so k runs over 1, 2, …, n (0 is excluded)
* "the reciprocals of the squares"        → the summand `1 / (k : ℝ) ^ 2`, computed in the reals
* "1 + 1/4 + 1/9 + 1/16 + ⋯" (the sum)    → the partial sums `∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2`
  and their limit as n → ∞ (the infinite sum is the limit of its partial sums)
* "is … = π²/6"                           → for every ε > 0 there is N with
  `|partial sum − π ^ 2 / 6| < ε` for all n ≥ N, where `π` is `Real.pi`
-/

namespace TuriMath.ZetaTwo.B

open Real

/-- Euler (1734), the Basel problem: the partial sums `1 + 1/4 + ⋯ + 1/n²`
converge to `π² / 6`. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2) - π ^ 2 / 6| < ε

/-! ## Sanity section

The statement has a single hypothesis, `0 < ε`; it is satisfiable. -/

example : ∃ ε : ℝ, 0 < ε := ⟨1, one_pos⟩

/-! ## Concrete checks on small cases

The partial sums are the numbers in the source: 1, 1 + 1/4, 1 + 1/4 + 1/9, … -/

-- n = 1: the sum is 1.
example : (∑ k ∈ Finset.Icc (1 : ℕ) 1, 1 / (k : ℝ) ^ 2) = 1 := by
  norm_num

-- n = 2: 1 + 1/4 = 5/4.
example : (∑ k ∈ Finset.Icc (1 : ℕ) 2, 1 / (k : ℝ) ^ 2) = 5 / 4 := by
  rw [show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide]
  norm_num

-- n = 4: 1 + 1/4 + 1/9 + 1/16 = 205/144, the four terms written in the source.
example : (∑ k ∈ Finset.Icc (1 : ℕ) 4, 1 / (k : ℝ) ^ 2) = 205 / 144 := by
  rw [show Finset.Icc (1 : ℕ) 4 = {1, 2, 3, 4} by decide]
  norm_num

-- n = 0: the empty sum is 0 (k = 0 is never a term).
example : (∑ k ∈ Finset.Icc (1 : ℕ) 0, 1 / (k : ℝ) ^ 2) = 0 := by
  simp

-- The target is a real number in the right place: 205/144 ≈ 1.424 < π²/6 ≈ 1.645,
-- so the partial sums visibly approach it from below (π > 3 gives π²/6 > 3/2).
example : (205 / 144 : ℝ) < π ^ 2 / 6 := by
  have h := pi_gt_three
  nlinarith

-- The statement is not vacuous: a wrong target (say 1) fails at ε = 1/10 for n = 2,
-- since |5/4 − 1| = 1/4 ≥ 1/10.
example : ¬ |(5 / 4 : ℝ) - 1| < 1 / 10 := by
  norm_num [abs_of_pos]

end TuriMath.ZetaTwo.B
