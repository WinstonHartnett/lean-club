import Arithmetic.definition

open Nat_

theorem add_zero (m : Nat_) : m + zero = m := rfl

@[simp]
theorem add_succ (m n : Nat_) : m + succ n = succ (m + n) := rfl

theorem zero_add (m : Nat_) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ m hyp => 
    rw [add_succ]
    rw [hyp]

@[simp]
theorem succ_add (m n : Nat_) : succ m + n = succ (m + n) := by
  induction n with
  | zero => 
    rfl
  | succ n hyp =>
    rw [add_succ]
    rw [hyp]
    rw [←add_succ]

@[simp]
theorem add_comm (m n : Nat_) : m + n = n + m := by
  induction n with
  | zero => 
    rw [zero_add]
    rfl
  | succ n hyp =>
    rw [succ_add]
    rw [add_succ] 
    rw [hyp]
    
@[simp]
theorem add_assoc (l m n : Nat_) : (l + m) + n = l + (m + n) := by
  induction n with
  | zero => 
    rw [add_zero]
    rw [add_zero]
  | succ n hyp => 
    rw [add_succ]
    rw [add_succ]
    rw [add_succ]
    rw [hyp]

theorem mul_succ (m n : Nat_) : m * (succ n) = m + m * n := rfl

theorem zero_mul (n : Nat_) : zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n hyp => 
    rw [mul_succ]
    rw [hyp]
    rfl

theorem succ_mul (m n : Nat_) : (succ m) * n = n + m * n := by
  induction n with
  | zero => rfl
  | succ n hyp =>
    rw [mul_succ]
    rw [hyp]
    rw [mul_succ]
    rw [succ_add]
    rw [succ_add]
    rw [←add_assoc]
    rw [←add_assoc]
    simp
    

theorem mul_comm (m n : Nat_) : m * n = n * m := by
  induction m with
  | zero => 
    rw [zero_mul]
    rfl
  | succ m hyp => 
    rw [mul_succ]
    rw [succ_mul]
    rw [hyp]