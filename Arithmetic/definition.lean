inductive Nat_ where
  | zero : Nat_
  | succ : Nat_ → Nat_
  deriving Repr

namespace Nat_

def add (m n : Nat_) : Nat_ :=
  match n with
  | Nat_.zero => m
  | Nat_.succ n => Nat_.succ (add m n)

-- #eval add (succ (succ zero)) (succ zero)

instance : Add Nat_ where
  add := add

end Nat_