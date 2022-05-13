open Nat

-- def eqb (n m: Nat) : Bool :=
--   match n with
--   | zero => match m with
--             | zero => true
--             | succ m => false
--   | succ n => match m with
--               | zero => false
--               | succ m => eqb n m 
-- infix:101 " == " => eqb

def factorial (n: Nat) : Nat :=
  match n with
  | zero => 1
  | succ n => (succ n) * factorial n 

-- (S n) C (S k) = n C k + n C (S k)
def Binomial (n k: Nat) :=
  match n, k with
  | zero, _ => 1
  | _, zero => 1
  | succ n', succ k' => 
    if (n == k) then 1 else
    Binomial n' k' + Binomial n' k 

