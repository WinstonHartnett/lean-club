
def Weak : Prop -> Prop :=
  fun A => Not (Not A)

theorem weak_lem : (A : Prop) -> Weak (Or A (Not A)) := by
  intros A not_AvnA
  apply not_AvnA
  apply Or.inr
  intro a
  apply not_AvnA
  apply Or.inl
  exact a

theorem weak_dne : (A : Prop) -> Weak (Weak A -> A) := by
  intros A nwAtA
  apply nwAtA
  intro wA
  apply False.elim
  apply wA
  intro a
  apply nwAtA
  intro wA2
  exact a

open Classical
theorem strong_lem : (A : Prop) -> (Or A (Not A)) := em

theorem strong_dne : (A : Prop) -> Weak A -> A := by
  intros A wA
  cases em A with
  | inl a => exact a
  | inr nA =>
    apply False.elim
    exact wA nA

