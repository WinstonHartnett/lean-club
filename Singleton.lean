def Implies (a b : Prop) : Prop := a → b
#check Implies

def UDonor : Type -> Prop := by
  intro A
  exact forall (B : Type), A -> B


#check Exists

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  <0, h>