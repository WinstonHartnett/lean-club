open Nat

#check Exists.intro

def divides (d n: Nat) : Prop :=
  exists (k: Nat), d * k = n

-- def divs (d n k: Nat) : Prop := d * k = n

-- def div_type (d n: Nat) := Σ Nat (divs d n)

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

theorem div_refl : forall n, n | n := by
  intro n
  have h: n * 1 = n := by simp
  exact (Exists.intro 1 h)

theorem div_trans : forall d n m, d | n -> n | m -> d | m := by
  intro d n m h1 h2
  cases h1 with
  | intro w1 h1 => cases h2 with
    | intro w2 h2 =>
      apply Exists.intro (w1 * w2)
      rw [<-Nat.mul_assoc]
      rw [h1]; assumption
