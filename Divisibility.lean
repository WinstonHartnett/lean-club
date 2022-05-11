open Nat

#check Exists.intro

def divides (d n: Nat) : Prop :=
  exists (k: Nat), d * k = n
-- def divides_type (m n: Nat) : Σ (k: Nat), (m * k = n) :=
--   sorry

infix:101 " | " => divides

theorem all_divides_zero : forall d, d | 0 := by
  intro d
  have h: d * 0 = 0 := by rfl 
  exact (Exists.intro 0 h)

theorem only_zero_divides_zero : forall n, 0 | n -> n = 0 := by
  unfold divides 
  intro n hyp
  cases hyp with
  | intro k hyp =>
      rw [<-hyp]
      rw [Nat.mul_comm]
      rfl
  
theorem one_divides_all : forall n, 1 | n := by
  intro n
  have h: 1 * n = n := by
    induction n with 
    | zero => rfl 
    | succ n ih_n => 
        rw [mul_succ]
        rw [ih_n]
  exact (Exists.intro n h)
