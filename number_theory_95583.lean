import Mathlib

/- The sum of $18$ consecutive positive integers is a perfect square. The smallest possible value of this sum is
(A) 169 (B) 225 (C) 289 (D) 361 (E) 441 -/
theorem number_theory_95583 :
IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 18, (k + i) ∧ ∃ m, m^2 = n} 225 := by
  -- obtain a formula for the sum in the problem statement
  have h: ∀ k: ℕ, ∑ i ∈ Finset.range 18, (k + i) = 18 * k + 153 := by
    intro k; calc
    ∑ i ∈ Finset.range 18, (k + i)
      = ∑ _ ∈ Finset.range 18, k + ∑ i ∈ Finset.range 18, i := by rw [Finset.sum_add_distrib]
    _ = 18 * k + ∑ i ∈ Finset.range 18, i                    := by rw [Finset.sum_const]; simp
    _ = 18 * k + 17 * 18 / 2                                  := by rw [Finset.sum_range_id]
    _ = 18 * k + 153                                          := by rfl
  -- show that 225 is in the set; it is the sum of $4+...+21$, and it is $15^2$
  constructor; rw [Set.mem_setOf]; use 4; simp [h]; use 15; rfl
  -- unwrap what it means to show that 225 is a lowerBound of the set
  -- for every x, which is in the set (hkx), and a perfect square $x=m^2$ (hm), we must show $225≤x$
  rw [mem_lowerBounds]; intros x hx; rw [Set.mem_setOf] at hx
  obtain ⟨k, hkx, m, hm⟩ := hx
  rw [h, ←hm] at hkx
  -- Do a case distinction. For $k≥4$ the claim follows because $x = 18 * k + 153 ≥ 225$.
  -- For the others check that $x$ is not a perfect square in this case
  match k with
  | 0 => apply False.elim; apply @Nat.not_exists_sq' 12 153; simp; simp; exact ⟨m, hkx⟩
  | 1 => apply False.elim; apply @Nat.not_exists_sq' 13 171; simp; simp; exact ⟨m, hkx⟩
  | 2 => apply False.elim; apply @Nat.not_exists_sq' 13 189; simp; simp; exact ⟨m, hkx⟩
  | 3 => apply False.elim; apply @Nat.not_exists_sq' 14 207; simp; simp; exact ⟨m, hkx⟩
  | k + 4 => rw [←hm, hkx]; linarith
