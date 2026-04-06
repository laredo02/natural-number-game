-- Level 1 / 5 : zero_add
theorem zero_add (n : ℕ) : 0 + n = n := by
induction n with d hd
rw [add_zero]
rfl
rw [add_succ]
rw [hd]
rfl

-- Level 2 / 5 : succ_add
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
induction b with h hd
rw [add_zero, add_zero]
rfl
nth_rewrite 2 [add_succ]
rw [add_succ, hd]
rfl

-- Level 3 / 5 : add_comm (level boss)
theorem add_comm (a b : ℕ) : a + b = b + a := by
induction b with h hd
rw [add_zero, zero_add]
rfl
rw [add_succ, succ_add, hd]
rfl

-- Level 4 / 5 : add_assoc (associativity of addition)
theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
induction c with h hd
rw [add_zero, add_zero]
rfl
rw [add_succ, add_succ, add_succ, hd]
rfl

-- Level 5 / 5 : add_right_comm
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
rw [add_assoc]
rw [add_comm b c, add_assoc]
rfl
