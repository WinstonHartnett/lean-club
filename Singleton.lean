def UDonor : Prop -> Prop := by
  intro A
  exact A -> forall (B : Prop), B

theorem not_eq_ud : forall (A : Prop), Not A <-> UDonor A := by
  intro A
  apply Iff.intro
  intro nA a B
  apply False.elim
  exact nA a
  intro udA a
  exact udA a False

#check Exists

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

