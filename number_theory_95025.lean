import Mathlib
open Nat

/- The increasing sequence 1,3,4,9,10,12,13,... consists of all those positive
integers which are powers of 3 or sums of distinct powers of 3. Find the
100th term of this sequence -/
/- In our definition of the set, also 0 is included since it is an empty
sum of distinct powers of 3. Since this is not wanted in the sequence we
calculate the 101st member of the set. -/
theorem number_theory_95025:
    (Nat.nth {x | ∀ l ∈ digits 3 x, l < 2} 100) = 981 := by
  let S: Set ℕ := {x | ∀ l ∈ digits 3 x, l < 2}
  let f: ℕ → ℕ := fun n => ofDigits 2 (digits 3 n)
  let g: ℕ → ℕ := fun n => ofDigits 3 (digits 2 n)

  /- First claim: f(g(n)) = n -/
  have claim1 (n: ℕ): f (g n) = n := by
    show ofDigits 2 (digits 3 (ofDigits 3 (digits 2 n))) = n
    rw [digits_ofDigits, ofDigits_digits]; simp
    intro l hl
    suffices l < 2 by linarith
    exact digits_lt_base one_lt_two hl
    intro h
    exact Nat.getLast_digit_ne_zero 2 (digits_ne_nil_iff_ne_zero.mp h)

  /- Second claim: g(f(n)) = n if n∈S -/
  have claim2 (n: ℕ): (n ∈ S) → g (f n) = n := by
    intro hn
    show ofDigits 3 (digits 2 (ofDigits 2 (digits 3 n))) = n
    rw [digits_ofDigits, ofDigits_digits]; simp
    exact hn
    intro h
    exact Nat.getLast_digit_ne_zero 3 (digits_ne_nil_iff_ne_zero.mp h)

  /- We'll need the values f(0) = 0 and g(0) = 0 -/
  have f_zero: f 0 = 0 := by
    show ofDigits 2 (digits 3 0) = 0; rfl
  have g_zero: g 0 = 0 := by
    show ofDigits 3 (digits 2 0) = 0; rfl

  /- Third claim: g is strictly monotonous.
    We'll show this by induction on n, hence the let rec -/
  let rec claim3: StrictMono g
    | 0 => by
        intros n hn
        apply by_contradiction; intro hc
        have _: g n = 0 := by linarith
        have _: f (g n) = f 0 := by simp [*]
        rw [f_zero, claim1] at *
        linarith
    | n + 1 => by
      intros m hlt
      show ofDigits 3 (digits 2 (n + 1)) < ofDigits 3 (digits 2 m)
      rw [digits_eq_cons_digits_div]
      nth_rw 2 [digits_eq_cons_digits_div]
      rw [ofDigits_cons, ofDigits_cons]
      show (n + 1) % 2 + 3 * g ((n + 1) / 2) < m % 2 + 3 * g (m / 2)
      have le_halves: (n + 1) / 2 ≤ m / 2 := by apply Nat.div_le_div_right; exact hlt.le
      match le_halves.lt_or_eq with
        | Or.inl hlt₂ =>
            have ih: g ((n + 1) / 2) < g (m / 2) := claim3 hlt₂
            cases Nat.mod_two_eq_zero_or_one (n + 1)
            <;> cases Nat.mod_two_eq_zero_or_one m
            <;> rw [← mod_add_div' (n+1) 2, ← mod_add_div' m 2 ] at hlt
            <;> linarith
        | Or.inr heq =>
            simp [heq]
            cases Nat.mod_two_eq_zero_or_one (n + 1)
            <;> cases Nat.mod_two_eq_zero_or_one m
            <;> rw [← mod_add_div' (n+1) 2, ← mod_add_div' m 2 ] at hlt
            <;> linarith
      all_goals linarith

  /- Fourth claim: Also f is strictly monotonous on S. -/
  have claim4: (m: ℕ) → (m ∈ S) → (n: ℕ) → (n ∈ S) → (m < n) → (f m < f n) := by
    intros m hm n hn hlt; apply by_contradiction; intro hle
    have hle: f n ≤ f m := by linarith
    match (le_iff_lt_or_eq.mp hle) with
    | Or.inl hlt =>
        have : g (f n) < g (f m) := claim3 hlt
        rw [claim2 n hn, claim2 m hm] at this; linarith
    | Or.inr heq =>
        have : g (f n) = g (f m) := by simp [heq]
        rw [claim2 n hn, claim2 m hm] at this; linarith

  /- We have shown that $f$ and $g$ define a monotonous bijection between $S$ and ℕ
  and it remains to prove that in this case the n-th element of $S$ is equal to
  g(n). For this we need the following three calculations: -/

  have g_mem_S (n: ℕ): g n ∈ S :=
    show ∀ l∈ digits 3 (ofDigits 3 (digits 2 n )), l < 2 by
    rw [digits_ofDigits]; intros l hl; apply digits_lt_base
    simp; assumption; simp;
    intros l hl; have : _ := digits_lt_base one_lt_two hl; linarith
    intro h; rw [digits_ne_nil_iff_ne_zero] at h;
    apply getLast_digit_ne_zero; assumption

  have S_zero: nth S 0 = 0 := by
    apply nth_zero_of_zero;
    show ∀ l ∈ digits 3 0, l < 2; simp

  have S_inf: S.Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro n
    use g (n + 1); apply And.intro;
    exact g_mem_S (n+1)
    linarith [StrictMono.id_le claim3 (n+1)]

  let rec claim5: (n: ℕ) → Nat.nth S n = g n
  | 0 => by rw [S_zero, g_zero]
  | n+1 => by
      apply eq_of_le_of_le
      have g_lt: g n < g (n+1) := claim3 (by linarith)
      rw [← (claim5 n)] at g_lt
      apply by_contradiction
      intro hc; have hc: (g (n+1) < nth S (n+1)) := by linarith
      have hc := le_nth_of_lt_nth_succ hc (g_mem_S (n + 1))
      linarith
      apply by_contradiction
      intro; have hc: nth S (n+1) < g (n+1) := by linarith
      have hf :f (nth S (n+1)) < f (g (n+1)) := by
        apply claim4; rw [Set.mem_def]
        apply nth_mem_of_infinite
        assumption; exact g_mem_S (n+1); assumption
      rw [claim1] at hf
      have hf2: f (nth S n) < f (nth S (n+1)):= by
        apply claim4 <;> try rw [Set.mem_def] <;> apply nth_mem_of_infinite <;> assumption
        rw [nth_lt_nth] ; simp; assumption
      rw [claim5 n, claim1] at hf2; linarith

  /- Now we can finish off the problem. -/
  show Nat.nth S 100 = 981
  rw [claim5 100]
  show ofDigits 3 (digits 2 100) = 981
  rfl
