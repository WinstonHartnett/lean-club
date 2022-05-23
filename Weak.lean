
def DNot : Prop -> Prop :=
  fun A => Not (Not A)

theorem weak_lem : (A : Prop) -> DNot (Or A (Not A)) := by
  intro A not_lem
  apply not_lem
  apply Or.inr
  intro a
  apply not_lem
  apply Or.inl
  exact a

theorem weak_dne : (A : Prop) -> DNot (DNot A -> A) := by
  intro A not_dne
  apply not_dne
  intro not_not_A
  apply False.elim
  apply not_not_A
  intro a
  apply not_dne
  intro ignore
  exact a

open Classical
theorem strong_lem : (A : Prop) -> (Or A (Not A)) := em

theorem strong_dne : (A : Prop) -> DNot A -> A := by
  intro A not_not_A
  cases em A with
  | inl a => exact a
  | inr not_A =>
    apply False.elim
    exact not_not_A not_A

