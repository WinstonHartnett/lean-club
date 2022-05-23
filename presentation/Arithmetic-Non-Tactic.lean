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
  | succ n => (multiply m n) + m

instance : HMul Nat_ Nat_ Nat_ where
  hMul := multiply

end Nat_

-- PROOFS

open Nat_

theorem add_zero (m : Nat_) : m + zero = m := rfl

theorem add_succ (m n : Nat_) : m + succ n = succ (m + n) := rfl

theorem zero_add (m : Nat_) : zero + m = m :=
  match m with
  | zero => rfl
  | succ k => congrArg succ (zero_add k)

theorem succ_add (m n : Nat_) : succ m + n = succ (m + n) :=
  match n with
  | zero => rfl
  | succ k => congrArg succ (succ_add m k)

theorem add_comm (m n : Nat_) : m + n = n + m :=
  match m with
  | zero => zero_add n
  | succ k => Eq.trans (succ_add k n)
                (congrArg succ (add_comm k n))
    
theorem add_assoc (l m n : Nat_) : (l + m) + n = l + (m + n) :=
  match n with
  | zero => rfl
  | succ k => congrArg succ (add_assoc l m k)

theorem add_left_assoc_flip (l m n : Nat_) : l + (m + n) = m + (l + n) :=
  Eq.trans (Eq.symm (add_assoc l m n))
    (Eq.trans (congrArg (. + n) (add_comm l m))
      (add_assoc m l n))

theorem add_right_assoc_flip (l m n : Nat_) : l + m + n = l + n + m :=
  Eq.trans (add_assoc l m n)
    (Eq.trans (congrArg (l + .) (add_comm m n))
      (Eq.symm (add_assoc l n m)))

theorem mul_zero (n : Nat_) : n * zero = zero := rfl

theorem mul_succ (m n : Nat_) : m * (succ n) = m * n + m := rfl

theorem zero_mul (n : Nat_) : zero * n = zero :=
  match n with
  | zero => rfl
  | succ k => zero_mul k

theorem succ_mul (m n : Nat_) : (succ m) * n = m * n + n :=
  match n with
  | zero => rfl
  | succ k => Eq.trans (congrArg (. + succ m) (succ_mul m k) )
                (congrArg succ (add_right_assoc_flip _ k m))

theorem mul_comm (m n : Nat_) : m * n = n * m :=
  match m with
  | zero => zero_mul n
  | succ k => Eq.trans (succ_mul k n)
                (congrArg (. + n) (mul_comm k n))
  
theorem distr_r (l m n : Nat_) : (l + m) * n = l * n + m * n :=
  match n with
  | zero => rfl
  | succ k => Eq.trans (congrArg (. + (l + m)) (distr_r l m k))
                (Eq.trans (add_assoc (l*k) (m*k) (l+m))
                  (Eq.trans (congrArg (l*k + .)
                              (add_left_assoc_flip (m*k) l m))
                    (Eq.symm (add_assoc (l*k) l (m*k+m)))))

theorem distr_l (l m n : Nat_) : l * (m + n) = l * m + l * n :=
  Eq.trans (mul_comm l (m+n))
    (Eq.trans (distr_r m n l)
      (Eq.trans (congrArg (. + n*l) (mul_comm m l))
        (congrArg (l*m + .) (mul_comm n l))))

theorem mul_assoc (l m n : Nat_) : (l * m) * n = l * (m * n) :=
  match n with
  | zero => rfl
  | succ k => Eq.trans (congrArg (. + l*m) (mul_assoc l m k))
                (Eq.symm (distr_l l (m*k) m))

def nat_to_prop (n : Nat_) : Prop :=
  match n with
  | zero => False
  | succ k => True
theorem snz_helper (n: Nat_) : succ n = zero -> nat_to_prop zero :=
  fun sneo => Eq.subst sneo True.intro
theorem succ_neq_zero (n: Nat_) : succ n = zero -> False :=
  snz_helper n