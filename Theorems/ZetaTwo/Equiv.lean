import Theorems.ZetaTwo.A
import Theorems.ZetaTwo.B

/-!
# ZetaTwo: A ↔ B

A says `HasSum` over `ℕ+` of `1/n²` is `π²/6`; B says the partial sums over `Icc 1 n`
converge to `π²/6` in the ε–N sense. We match them: reindex `ℕ+ → ℕ` (the `n = 0` term is `0`),
use that for nonnegative terms `HasSum` is convergence of partial sums, then unfold the metric limit.
-/

namespace TuriMath.ZetaTwo

open Filter Topology

private noncomputable def f (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

private lemma f_nonneg (n : ℕ) : 0 ≤ f n := by unfold f; positivity

private lemma A_iff_nat (s : ℝ) : HasSum A.term s ↔ HasSum f s := by
  have hinj : Function.Injective (fun n : ℕ+ => (n : ℕ)) := PNat.coe_injective
  refine (hinj.hasSum_iff (f := f) (a := s) ?_)
  intro x hx
  have : x = 0 := by
    by_contra h
    exact hx ⟨⟨x, Nat.pos_of_ne_zero h⟩, rfl⟩
  simp [f, this]

private lemma sum_Icc (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 = ∑ k ∈ Finset.range (n + 1), f k := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
  have : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by ext x; simp [Finset.mem_Ico, Finset.mem_Icc]
  simp [f, this]

theorem equiv : A.Statement ↔ B.Statement := by
  unfold A.Statement B.Statement
  rw [A_iff_nat, hasSum_iff_tendsto_nat_of_nonneg f_nonneg, ← tendsto_add_atTop_iff_nat 1,
    Metric.tendsto_atTop]
  simp only [sum_Icc, Real.dist_eq]

end TuriMath.ZetaTwo
