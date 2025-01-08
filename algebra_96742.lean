import Mathlib

/- For how many ordered pairs of positive integers $(x,y)$ is $x+2y=100$?
(A) 33 (B) 49 (C) 50 (D) 99 (E) 100 -/
theorem algebra_96742 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x + 2 * y = 100}.ncard = 49 := by
  -- Define a function from {0, ..., 48} to our set
  -- It is enough to show that f is surjective onto our set,
  -- its image is contained in our set and f is injective
  let f : (n : ℕ) → (h: n < 49) → ℕ × ℕ := fun n => fun _ => (98 - 2 * n, n + 1)
  apply Set.ncard_eq_of_bijective f
  -- Surjectivity. If (n, m) is in the set, then it is f(m-1)
  · intro (n, m); intro hnm
    rw [Set.mem_setOf] at hnm
    simp at hnm; obtain ⟨hn, hm, hnm⟩ := hnm
    use (m - 1); use (by omega)
    show (98 - 2 * (m - 1), (m - 1) + 1) = (n, m); simp; apply And.intro
    <;> omega
  -- Image of f contained in the set. Follows from calculation
  · intros n hn
    rw [Set.mem_setOf]; simp; apply And.intro
    <;> omega
  -- Injectivity follows by comparing the second components
  · intros n m _ _ hnm;
    have hnm : (98 - 2 * n, n + 1) = (98 - 2 * m, m + 1) := by exact hnm
    simp at hnm; exact hnm.right
