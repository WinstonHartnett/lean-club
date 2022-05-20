open Nat

inductive Vec (A : Type) : Nat -> Type u where
  | vn : Vec A zero
  | vc : A -> {k : Nat} -> (Vec A k) -> (Vec A (succ k))
  deriving Repr
def Vec.head (A : Type) (k : Nat) (v : Vec A (succ k)) : A :=
  match v with
  | vc h t => h
def Vec.tail (A : Type) (k : Nat) (v : Vec A (succ k)) : Vec A k :=
  match v with
  | vc h t => t
namespace Vec

def PNN : Type := Prod Nat Nat
def add_to_cdr (k : Nat) (v : Vec PNN k)
  : Vec PNN k :=
  match k with
  | zero => vn
  | succ t =>
    vc ((head PNN t v).1, succ (head PNN t v).2)
      (add_to_cdr t (tail PNN t v))

def diagN (n : Nat) : Vec PNN (succ n) :=
  match n with
  | zero => vc (0,0) vn
  | succ k =>
    vc (succ k, 0) (add_to_cdr (succ k) (diagN k))

#eval diagN 5
