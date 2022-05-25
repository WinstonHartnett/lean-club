-- DEFINITIONS 
inductive Nat_ where
  | zero : Nat_
  | succ : Nat_ → Nat_
  deriving Repr

namespace Nat_

def add (m n : Nat_) : Nat_ :=
  match n with
  | zero => m
  | succ n => succ (add m n)

-- #eval add (succ (succ zero)) (succ zero)
instance : Add Nat_ where
  add := add

def multiply (m n : Nat_) : Nat_ :=
  match n with
  | zero => zero
  | succ n => m + (multiply m n)

instance : HMul Nat_ Nat_ Nat_ where
  hMul := multiply

#eval multiply (succ (succ zero)) (succ (succ zero))
#eval (succ (succ zero)) * (succ (succ zero))

end Nat_

-- PROOFS

open Nat_

@[simp]
theorem add_zero (m : Nat_) : m + zero = m := rfl

@[simp]
theorem add_succ (m n : Nat_) : m + succ n = succ (m + n) := rfl

@[simp]
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

theorem add_comm (m n : Nat_) : m + n = n + m := by
  induction n with
  | zero => 
    simp
  | succ n hyp =>
    simp
    rw [hyp]
    
theorem add_assoc (l m n : Nat_) : (l + m) + n = l + (m + n) := by
  induction n with
  | zero => 
    -- repeat (rw [add_zero])
    simp
  | succ n hyp => 
    -- repeat (rw [add_succ])
    simp
    rw [hyp]

theorem add_assoc_flip (l m n : Nat_) : l + (m + n) = m + (l + n) := by
  rw [←add_assoc]
  rw [←add_assoc]
  rw [add_comm l m]

theorem mul_succ (m n : Nat_) : m * (succ n) = m + m * n := rfl

theorem mul_zero (n : Nat_) : n * zero = zero := rfl

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
    repeat (rw [succ_add])
    repeat (rw [←add_assoc])
    rw [add_comm m _]
    

theorem mul_comm (m n : Nat_) : m * n = n * m := by
  induction m with
  | zero => 
    rw [zero_mul]
    rfl
  | succ m hyp => 
    rw [mul_succ]
    rw [succ_mul]
    rw [hyp]
  
theorem distr_r (l m n : Nat_) : (l + m) * n = l * n + m * n := by
  induction n with
  | zero => 
    repeat (rw [mul_zero])
    rfl
  | succ n hyp =>
    calc 
      (l + m) * succ n = (l + m) + (l + m) * n := by rw [mul_succ]
      _ = ((l + m) * n + l) + m                := by rw [add_comm]; rw[add_assoc]
      _ = (l + (l + m) * n ) + m               := by rw [add_comm _ ((l + m) * n)]
      _ = (l + l * n + m * n) + m              := by rw [hyp]; rw [add_assoc _ (l*n)]
      _ = l * (succ n) + m * n + m             := by rw [mul_succ]
      _ = l * (succ n) + (m * n + m)           := by rw [add_assoc]
      _ = l * (succ n) + m * (succ n)          := by rw [add_comm (m*n) m]; rw [←mul_succ]

theorem distr_l (l m n : Nat_) : l * (m + n) = l * m + l * n := by
  rw [mul_comm]
  rw [distr_r]
  rw [mul_comm]
  rw [mul_comm n]
 

theorem mul_assoc (l m n : Nat_) : (l * m) * n = l * (m * n) := by
  induction n with
  | zero =>
    repeat (rw [mul_zero])
  | succ n hyp => 
    rw [mul_succ m]
    rw [mul_succ]
    rw [distr_l]
    rw [hyp]

theorem succ_neq_zero (n: Nat_) : succ n = zero -> false := by
    intro hyp
    injection hyp