import Mathlib

/- If $∑_{n=0}^∞ cos^⁡(2n) θ = 5$, what is the value of $cos (2θ)$?
(A) 1/5 (B) 2/5 (C) √5/5 (D) 3/5 (E) 4/5 -/
theorem algebra_96688 (θ : ℝ) (h : ∑' n : ℕ, (Real.cos θ)^(2 * n) = 5) :
Real.cos (2 * θ) = 3/5 := by
  -- Write the assumption h as a geometric series in $cos^2 θ$
  simp [mul_comm, pow_mul'] at h

  -- Show that $cos^2 θ < 1$, so that we can apply the geometric series
  have hcos: (Real.cos θ)^2 < 1 := by
    have : (Real.cos θ)^2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one]; apply Real.abs_cos_le_one
    cases this.eq_or_lt
    simp [*] at h
    assumption

  -- Calculate
  have h' : 1 / (1 - (Real.cos θ)^2) = 5 := by calc
    1 / (1 - (Real.cos θ)^2) = (1 - (Real.cos θ)^2)⁻¹ := by exact one_div (1 - (Real.cos θ)^2)
                           _ = ∑' n : ℕ, ((Real.cos θ) ^ 2) ^ n := by rw [tsum_geometric_of_lt_one]; apply sq_nonneg; assumption
                           _ = 5                                := by assumption

  -- To eliminate the fraction we need that the denominator is nonzero
  have : (1 - (Real.cos θ)^2) ≠ 0 := by linarith
  have : 1 = 5 * (1 - (Real.cos θ)^2) := by exact (mul_inv_eq_iff_eq_mul₀ this).mp h'

  -- Now we can easily calculate $cos(2θ)$ using the angle duplication formula
  -- Real.cos_two_mul
  have : (Real.cos θ) ^ 2 = 4 / 5 := by linarith
  field_simp [Real.cos_two_mul, this]; linarith
