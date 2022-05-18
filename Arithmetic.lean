open Nat

-- Nat definition
-- Enclosed in namespace to avoid polluting main namespace
namespace defs
  inductive nat : Type
    | zero : nat
    | succ : nat -> nat

  /- Note that addition and multiplication recurse on the second argument.
    This is the way that Lean defines addition; it could just as easily
    have chosen the other direction. This just means we usually apply
    induction on the second variable. -/
  def add (m n : Nat) : Nat :=
    match n with
    | zero   => m
    | succ n => succ (add m n)

theorem add_succ (m n : Nat_) : m + succ n = succ (m + n) := rfl

theorem _add_zero : forall (n: Nat), n + 0 = n := by
  intro n; rfl

theorem _add_succ : forall (n m: Nat), n + succ m = succ (n + m) := by
  intro n m; rfl

theorem _zero_add : forall (n: Nat), 0 + n = n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih_n =>
      rw [_add_succ]
      rw [ih_n]

theorem _succ_add : forall (n m: Nat), succ n + m = succ (n + m) := by
  intro n m
  induction m with
  | zero => rfl
  | succ m hyp =>
      rw [_add_succ]
      rw [_add_succ, hyp]

theorem _add_comm : forall (n m: Nat), n + m = m + n := by
  intro n; induction n with
  | zero =>
      intro m
      rw [_zero_add]
      rfl
  | succ n ih_n => 
      intro m
      rw [_succ_add]
      rw [_add_succ]
      rw [ih_n]

theorem _add_assoc : forall (n m k: Nat), n + (m + k) = (n + m) + k := by
  intro n m k; induction k with 
  | zero => rfl
  | succ k ih_k =>
      rw [_add_succ]
      rw [_add_succ]
      rw [ih_k]
      rfl

theorem _assoc_flip : forall (n m k: Nat), n + (m + k) = m + (n + k) := by
  intro n m k 
  rw [_add_assoc]
  rw [_add_assoc]
  rw [_add_comm n m]

theorem _mul_zero : forall (n: Nat), n * 0 = 0 := by
  intro n; rfl

theorem _mul_succ : forall (n m: Nat), n * (succ m) = n * m + n := by
  intro n m; rfl

theorem _zero_mul : forall (n: Nat), 0 * n = 0 := by
  intro n; induction n with 
  | zero => rfl 
  | succ n ih_n =>
      rw [_mul_succ]
      rw [ih_n]

theorem _succ_mul : forall (n m: Nat), (succ n) * m = m + n * m := by
  intro n m; induction m with 
  | zero => rfl 
  | succ m ih_m =>
      rw [_mul_succ]
      rw [ih_m]
      rw [_add_succ]
      rw [_succ_add]
      rw [_mul_succ]
      rw [_add_assoc]

theorem _mul_comm : forall (n m: Nat), n * m = m * n := by
  intro n m; induction n with
  | zero =>
      rw [_zero_mul]
      rfl
  | succ n ih_n =>
      rw [_succ_mul, _mul_succ]
      rw [ih_n]
      rw [_add_comm]

theorem _right_distr : forall (n m k: Nat), (n + m) * k = n * k + m * k := by
  intro n m k; induction k with 
  | zero => rfl 
  | succ k ih_k =>
      rw [_mul_succ, _mul_succ, _mul_succ]
      rw [ih_k]
      rw [<- _add_assoc]
      rw [_assoc_flip (m*k)]
      rw [_add_assoc]

theorem _left_distr : forall (n m k: Nat), n * (m + k) = n * m + n * k := by
  intro n m k
  rw [_mul_comm]
  rw [_right_distr]
  rw [_mul_comm, _mul_comm k]

theorem _mul_assoc : forall (n m k: Nat), n * (m * k) = (n * m) * k := by
  intro n m k; induction k with
  | zero => rfl 
  | succ k ih_k => 
      rw [_mul_succ, _mul_succ]
      rw [_left_distr]
      rw [ih_k]

theorem succ_not_zero : forall (n: Nat), succ n = 0 -> false := by
  intros n hyp
  injection hyp /- the injection tactic exploits the fact that
    constructors of an inductive type are injective,
    so succ n = 0 immediately solves any goal. -/
