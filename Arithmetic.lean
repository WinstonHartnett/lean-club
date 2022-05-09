import Arithmetic.definition

open Nat_

theorem add_zero (m : Nat_) : m + zero = m := rfl

theorem add_succ (m n : Nat_) : m + succ n = succ (m + n) := rfl

theorem zero_add (m : Nat_) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ m hyp => 
    rw [add_succ]
    rw [hyp]

theorem succ_add_eq_add_succ (m n : Nat_) : succ m + n = m + succ n := by
  induction n with
  | zero => 
    rfl
  | succ n hyp =>
    rw [add_succ]
    rw [hyp]
    rw [←add_succ]
