import Theorems.ZetaTwo.A

/-!
# ZetaTwo: proof of A.Statement

Not a citation of `hasSum_zeta_two`. We start from the Fourier-series / Bernoulli-polynomial
identity `hasSum_one_div_nat_pow_mul_cos` (k = 1, x = 0), evaluate B₂(0) = 1/6, and
reindex from `ℕ` (where the n = 0 term is 0) to `ℕ+`.
-/

namespace TuriMath.ZetaTwo

open Real

theorem main : A.Statement := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero
    (Set.left_mem_Icc.mpr zero_le_one)
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := by
    convert h using 1
    · ext n; simp
    · have : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval 0 = (1 / 6 : ℝ) := by
        rw [Polynomial.eval_zero_map, Polynomial.bernoulli_eval_zero]
        rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 * 1 ≠ 1)]
        norm_num [bernoulli'_two]
      rw [this]
      simp [Nat.factorial]; ring
  unfold A.Statement
  have hinj : Function.Injective (fun n : ℕ+ => (n : ℕ)) := PNat.coe_injective
  have h3 := (hinj.hasSum_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (a := π ^ 2 / 6) ?_).mpr h2
  · exact h3
  · intro x hx
    have : x = 0 := by
      by_contra hne
      exact hx ⟨⟨x, Nat.pos_of_ne_zero hne⟩, rfl⟩
    simp [this]

end TuriMath.ZetaTwo
