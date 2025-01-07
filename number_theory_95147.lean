import Mathlib

/- Let $P(n)$ and $S(n)$ denote the product and the sum, respectively, of the digits
of the integer $n$. For example, $P(23)=6$ and $S(23)=5$. Suppose $N$ is a
two-digit number such that $N=P(N)+S(N)$. What is the units digit of $N$?
(A) 2 (B) 3 (C) 6 (D) 8 (E) 9 -/
-- Define P and S as in the problem statement
def P (n : ℕ) := (Nat.digits 10 n).prod
def S (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_95147 {N : ℕ} (hN: List.length (Nat.digits 10 N)
= 2) (hN2 : N = P N + S N) : (Nat.digits 10 N)[0]? = some 9 := by
  -- Show by contradiction that $N ≠ 0$, as otherwise its digits
  -- wouldn't have length $2$
  have : N ≠ 0 := by
    intro h; rw [h, Nat.digits_zero] at hN; simp at hN;

  -- obtain the digits of $N$
  rw [List.length_eq_two] at hN
  obtain ⟨b, a, hab⟩ := hN

  -- obtain formulas for $P(N)$
  have : P N = b * a := by calc
    P N = (Nat.digits 10 N).prod := by rfl
      _ = [b, a].prod            := by rw [hab]
      _ = b * a                  := by simp
  -- and $S(N)$
  have : S N = b + a := by calc
    S N = (Nat.digits 10 N).sum := by rfl
      _ = [b, a].sum            := by rw [hab]
      _ = b + a                 := by simp
  -- and $N$ in terms of its digits.
  have : N = 10 * a + b := by calc
    N = Nat.ofDigits 10 (Nat.digits 10 N) := by rw [Nat.ofDigits_digits]
    _ = Nat.ofDigits 10 [b, a]            := by rw [hab]
    _ = 10 * a + b                        := by simp [Nat.ofDigits_cons, Nat.add_comm]
  -- Show that $b * a = 9 * a$ by plugging in the formulas into hN2
  have : b * a = 9 * a := by linarith
  -- Show that $a > 0$ in order to cancel $a$ from the above
  have : a ≠ 0 := by calc
    a = List.getLast [b, a] (by simp)    := by rfl
    _ = List.getLast (Nat.digits 10 N) _ := by simp [hab]
    _ ≠ 0                                := by apply Nat.getLast_digit_ne_zero 10; assumption
  have : a > 0 := by apply Nat.zero_lt_of_ne_zero; assumption
  -- Finish by showing that $b$ was the desired digit
  rw [hab]; simp; apply Nat.mul_right_cancel <;> assumption
