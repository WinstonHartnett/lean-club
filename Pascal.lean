open Nat

def sumN (n : Nat) (f : Nat -> Nat): Nat :=
  match n with
  | 0 => 0
  | succ k => (sumN k f) + (f k)

def factorial (n: Nat) : Nat :=
  match n with
  | zero => 1
  | succ k => (succ k) * factorial k
postfix:200 "!" => factorial

def pascal : Nat -> Nat -> Nat :=
  fun x =>
    match x with
    | zero => fun y => 1
    | succ k =>
      fun y => sumN (succ y) (pascal k)

theorem pascal_tri : forall (x y : Nat),
  (pascal (succ x) (succ y)) =
  (pascal (succ x) y) + (pascal x (succ y)) := by
  intros x y
  rfl

theorem rightwall : forall (x : Nat),
  pascal x 0 = 1 := by
  intro x
  induction x with
  | zero => rfl
  | succ k hk =>
    rw [pascal]
    simp
    rw [sumN, sumN, hk]

theorem binom : forall (x y : Nat),
  (pascal x y) * (y ! * x !) = (y+x)! := by
  intro x
  induction x with
  | zero =>
    intro y
    rw [pascal, factorial]
    simp
  | succ k hk =>
    intro y
    induction y with
    | zero =>
      rw [pascal, factorial]
      simp
      rw [sumN, sumN, rightwall]
      simp
    | succ t ht =>
      rw [pascal_tri, add_succ]
      rw [Nat.add_mul]
      rw [factorial, Nat.mul_assoc,
      Nat.mul_comm (succ t), <-Nat.mul_assoc]
      rw [ht]
      have hkst := hk (succ t)
      rw [factorial] at hkst
      rw [factorial, Nat.mul_left_comm (t !),
      Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm (t ! * k !),
      <-Nat.mul_assoc (succ t),]
      rw [hkst]
      rw [factorial, Nat.mul_comm,
      Nat.add_succ, Nat.succ_add,
       <-Nat.add_mul,
      add_succ, succ_add]

