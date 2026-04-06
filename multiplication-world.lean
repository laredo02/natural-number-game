-- Level 1 / 9 : mul_one
theorem mul_one (m : ℕ) : m * 1 = m := by
rw [one_eq_succ_zero, mul_succ, mul_zero, add_comm, add_zero]
rfl

-- Level 2 / 9 : zero_mul
theorem zero_mul (m : ℕ) : 0 * m = 0 := by
induction m with h hd
rw [mul_zero]
rfl
rw [mul_succ, hd]
simp

--Level 3 / 9 : succ_mul
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
induction b with h hd
rw [mul_zero, mul_zero, add_zero]
rfl
rw [succ_mul]
rfl

-- Level 4 / 9 : mul_comm
theorem mul_comm (a b : ℕ) : a * b = b * a := by
induction b with h hd
rw [zero_mul, mul_zero]
rfl
rw [succ_mul, mul_succ, hd]
rfl

-- Level 5 / 9 : one_mul
theorem one_mul (m : ℕ): 1 * m = m := by
rw [mul_comm, mul_one]
rfl

-- Level 6 / 9 : two_mul
theorem two_mul (m : ℕ): 2 * m = m + m := by
induction m with h hd
rw [mul_zero, add_zero]
rfl
rw [mul_succ, hd]
repeat rw [succ_eq_add_one]
symm
rw [two_eq_succ_one, one_eq_succ_zero, succ_eq_add_one, succ_eq_add_one, zero_add]
simp [add_assoc, add_comm h]

-- In favor of diversity of solutions, an alternative simpler version is:
-- rw [two_eq_succ_one, succ_mul, one_mul]
-- rfl

-- Level 7 / 9 : mul_add
theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
induction a with h hd
repeat rw [zero_mul]
simp
repeat rw [succ_mul]
rw [hd]
nth_rewrite 2 [add_assoc]
nth_rewrite 5 [add_comm]
nth_rewrite 3 [add_comm] -- Does this count as 5 rewrites?
simp [add_assoc]

-- Level 8 / 9 : add_mul
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
rw [mul_comm, mul_add]
rw [mul_comm, mul_comm c b]
rfl

-- Level 9 / 9 : mul_assoc
theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
induction c with h hd
repeat rw [mul_zero]
rfl
repeat rw [mul_succ]
rw [mul_add]
rw [hd]
rfl
