open Nat

-- Factorial
def factorial (n: Nat) : Nat :=
  match n with
  | zero => 1
  | succ n => (succ n) * factorial n
postfix:200 "!" => factorial

-- Combination: n choose k
def choose (n k: Nat) :=
  match n, k with
  | _, zero => 1
  | zero, succ _ => 0
  | succ n', succ k' => choose n' k' + choose n' k
infix:50 " C " => choose

-- Basic combination lemmas
@[simp] theorem choose_0 : forall (n: Nat), (n C 0) = 1 := by
  intro n
  unfold choose
  cases n with
  | zero => rfl
  | succ n => rfl

@[simp] theorem choose_1 : forall (n: Nat), (n C 1) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih_n =>
      unfold choose
      simp
      rw [ih_n, Nat.add_comm]

theorem choose_lt : forall (n m: Nat), n < m -> choose n m = 0 := by
  intro n; induction n with
  | zero =>
      intro m hyp
      cases m; cases hyp; rfl
  | succ n ih_n =>
      intro m hyp
      cases m with
      | zero => cases hyp
      | succ m =>
          unfold choose; simp
          have h1: (n C m) = 0 := by
            apply ih_n; apply lt_of_succ_lt_succ; assumption
          have h2: (n C succ m) = 0 := by
            apply ih_n; apply lt_of_succ_lt; assumption
          rw [h1, h2]

@[simp] theorem choose_same : forall (n: Nat), (n C n) = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih_n =>
      unfold choose
      simp
      rw [ih_n, choose_lt n (succ n) (lt.base n)]

theorem choose_pascal : forall (n k: Nat),
  (succ n C succ k) = (n C succ k) + (n C k) := by
  intro n k; conv => lhs; unfold choose; simp; rw [Nat.add_comm]

-- Lemma for choose_swap and choose_factorial
theorem succ_swap : forall (n m: Nat),
  succ n + m = n + succ m := by
  intro n m;
  induction m with
  | zero => rfl
  | succ m ih_m => rw [add_succ, add_succ, add_succ, succ_add]

theorem choose_swap : forall (n k: Nat),
  (n + k C k) = (n + k C n) := by
  intro n; induction n with
  | zero => intro k; simp
  | succ n ih_n =>
      intro k; induction k with
      | zero => simp
      | succ k ih_k =>
          conv => lhs; rw [add_succ]; unfold choose; simp;
                  arg 2; rw [succ_swap]
          conv => rhs; rw [succ_add]; unfold choose; simp;
                  arg 2; rw [<-succ_swap]
          rw [ih_k]; rw [ih_n]; rw [Nat.add_comm]

-- Alternative definition of choice function:
-- n! / (k! * (n-k)!) = n C k
theorem choose_factorial : forall (m n: Nat),
  ((n + m) C n) * (n ! * m !) = (n + m) ! := by
  intro m; induction m with
  | zero =>
      intro n; simp;
      have h: 0! = 1 := by rfl
      rw [h]; rw [Nat.mul_comm]; simp
  | succ m ih_m =>
      intro n; induction n with
      | zero =>
          unfold choose; simp;
          have h: 0! = 1 := by rfl
          rw [h, Nat.one_mul]
      | succ n ih_n =>
          rw [add_succ]; unfold choose; simp
          rw [Nat.right_distrib]
          rw [succ_swap]
          conv => lhs; args; args; 
                  skip; args; unfold factorial; simp
          conv => lhs; args;
                  rw [Nat.mul_assoc]; 
                  rw [<-Nat.mul_assoc _ (succ n)];
                  rw [Nat.mul_comm _ (succ n)];
                  rw [Nat.mul_assoc];
                  rw [ih_n]
          have h: (succ m)! = (succ m) * m ! := by rfl
          rw [h]; rw [<-Nat.mul_assoc (factorial (succ n))]
          rw [Nat.mul_comm _ (succ m)]
          rw [Nat.mul_assoc]
          rw [<-succ_swap]
          rw [<-Nat.mul_assoc]
          rw [Nat.mul_comm _ (succ m)]
          rw [Nat.mul_assoc]
          rw [ih_m]
          rw [<-Nat.right_distrib]
          rw [add_succ]
          rfl

-- Σ from k to k+n of f(k)
def sum_k_n (n k: Nat) (f: Nat -> Nat) : Nat :=
  match n with
  | zero => f k
  | succ n' => f k + sum_k_n n' (succ k) f

-- A number of useful theorems about sums
theorem sum_k_n_step : forall (n k: Nat) (f: Nat -> Nat),
  sum_k_n (succ n) k f = f k + sum_k_n n (succ k) f := by
  intro n k f; cases n with
  | zero => rfl
  | succ n => rfl

theorem sum_k_n_reduce : forall (n k: Nat) (f: Nat -> Nat),
  sum_k_n (succ n) k f = sum_k_n n k f + f (succ n + k) := by
  intro n k f; revert k
  induction n with
  | zero => intro k; rw [sum_k_n_step]; unfold sum_k_n; simp; rw [Nat.add_comm _ k]
  | succ n ih_n =>
      intro k
      rw [sum_k_n_step]
      rw [ih_n]
      rw [sum_k_n_step]
      have h: succ (succ n) + k = succ n + succ k := by
        rw [add_succ, <-succ_add]
      rw [h, Nat.add_assoc]

theorem sum_k_n_pred : forall (n k: Nat) (f: Nat -> Nat),
  sum_k_n n k f = sum_k_n n (succ k) (fun x => f (pred x)) := by
  intro n; induction n with
  | zero => intro k f; rfl
  | succ n ih_n =>
      intro k f
      rw [sum_k_n_step, sum_k_n_step]
      rw [ih_n]
      rfl

theorem add_swap : forall (a b c d: Nat),
  (a + b) + (c + d) = (a + c) + (b + d) := by
  intro a b c d
  rw [Nat.add_assoc]
  rw [<-Nat.add_assoc _ c]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc]
  rw [<-Nat.add_assoc]

theorem sum_k_n_combine : forall (n k: Nat) (f g: Nat -> Nat),
  sum_k_n n k f + sum_k_n n k g = sum_k_n n k (fun x => f x + g x) := by
  intro n
  induction n with
  | zero => intro k f g; rfl
  | succ n ih_n =>
      intro k f g
      rw [sum_k_n_step, sum_k_n_step, sum_k_n_step]
      rw [<-ih_n]
      rw [add_swap]

theorem sum_k_n_left_distrib : forall (n k x: Nat) (f: Nat -> Nat),
  x * (sum_k_n n k f) = sum_k_n n k (fun k => x * f k) := by
  intro n; induction n with
  | zero => intro k x f; rfl
  | succ n ih_n =>
      intro k x f
      rw [sum_k_n_step, sum_k_n_step]
      rw [Nat.left_distrib]
      rw [ih_n]

theorem sum_k_n_right_distrib : forall (n k x: Nat) (f: Nat -> Nat),
  (sum_k_n n k f) * x = sum_k_n n k (fun k => f k * x) := by
  intro n k x f
  rw [Nat.mul_comm]
  rw [sum_k_n_left_distrib]
  conv => rhs; args; skip; skip; intro k; rw [Nat.mul_comm]

theorem sum_k_n_reindex : forall (n k: Nat) (f: Nat -> Nat),
  sum_k_n n (succ k) f = sum_k_n n k (fun x => f (succ x)) := by
  intro n; induction n with
  | zero => intro k f; unfold sum_k_n; simp
  | succ n ih_n =>
      intro k f
      rw [sum_k_n_step]
      rw [sum_k_n_step]
      rw [ih_n]

theorem sum_k_n_extensional : forall (n k: Nat) (f g: Nat -> Nat),
  (forall x, x <= n -> f (k + x) = g (k + x)) ->
  sum_k_n n k f = sum_k_n n k g := by
  intro n; induction n with
  | zero =>
      intro k f g hyp;
      unfold sum_k_n; simp
      apply hyp 0; constructor
  | succ n ih_n =>
      intro k f g hyp;
      rw [sum_k_n_reduce, sum_k_n_reduce]
      have h1: forall x, x ≤ n → f (k + x) = g (k + x) := by
        intro x h2; apply hyp; constructor; apply h2
      specialize ih_n k f g h1
      rw [ih_n]
      have h2: f (k + succ n) = g (k + succ n) := by
        apply hyp; constructor
      rw [Nat.add_comm _ k]
      rw [h2]

-- cong from Pie
theorem cong : forall {X Y: Type} (f: X -> Y) (x x': X),
  x = x' -> f x = f x' := by
  intro X Y f x x' hyp; rw [hyp]

-- cong but on two arguments
theorem cong2 : forall {X Y Z: Type} (f: X -> Y -> Z) (x x': X) (y y': Y),
  x = x' -> y = y' -> f x y = f x' y' := by
  intro X Y Z f x x' y y' h1 h2; rw [h1, h2]

-- The binomial theorem.
-- Coefficients of the expansion of (x + y)^n are n C k.
def binomial_theorem : forall (x y n: Nat),
  (x + y)^n = sum_k_n n 0 (fun k => (n C k) * x^(n-k) * y^k) := by
  intro x y n; induction n with
  | zero => rfl
  | succ n ih_n =>
    rw [pow_succ]; rw [ih_n]
    cases n with
    | zero =>
        unfold sum_k_n; simp
        unfold sum_k_n; simp
        simp [pow_zero, pow_succ]
    | succ n' =>
        rw [Nat.left_distrib]
        rw [sum_k_n_right_distrib, sum_k_n_right_distrib]
        conv => lhs; arg 1; arg 3;
                intro k; rw [Nat.mul_assoc];
                rw [Nat.mul_comm _ x]; rw [<-Nat.mul_assoc];
                rw [Nat.mul_assoc _ _ x]; rw [<-pow_succ]
        conv => lhs; arg 2; arg 3;
                intro k; rw [Nat.mul_assoc]; rw[<-pow_succ]
        rw [sum_k_n_step]; rw [pow_zero]; simp
        rw [sum_k_n_reduce]; simp; rw [pow_zero]; simp
        rw [sum_k_n_pred n' 0]
        rw [<-Nat.add_assoc _ _ (y ^ succ (n' + 1))]
        rw [Nat.add_assoc (x ^ succ (succ n'))]
        rw [sum_k_n_combine]
        have h: (sum_k_n n' (succ 0) fun x_1 =>
          (succ n' C x_1) * x ^ succ (succ n' - x_1) * y ^ x_1 +
          (succ n' C pred x_1) * x ^ (succ n' - pred x_1) * y ^ succ (pred x_1))
          = (sum_k_n n' (succ 0) fun x_1 =>
            (succ (succ n') C x_1) * x ^ (succ (succ n') - x_1) * y ^ x_1) := by
            apply sum_k_n_extensional
            intro x_1 Hx_1
            rw [succ_add]; simp [succ_pred]
            rw [succ_sub_succ, succ_sub_succ]
            rw [choose_pascal (succ n')]
            rw [Nat.right_distrib, Nat.right_distrib]
            apply cong2
            -- first arg
            rw [Nat.mul_assoc, Nat.mul_assoc]
            apply cong
            rw [Nat.mul_comm, Nat.mul_comm _ (y ^ succ x_1)]
            apply cong
            apply cong
            rw [Nat.add_comm]
            rw [Nat.add_sub_assoc]
            rw [Nat.add_comm]
            assumption
            -- second arg
            rfl
        rw [h]
        rw [sum_k_n_step, sum_k_n_reduce]; simp [pow_zero, succ_add]
        rw [Nat.add_assoc]
  done

theorem one_pow : forall (n: Nat),
  1 ^ n = 1 := by
  intro n; induction n with
  | zero => rfl
  | succ n ih_n => rw [pow_succ, ih_n]

-- The sum of a row of Pascal's triangle is 2^n.
theorem pascal_row_sum : forall (n: Nat),
  sum_k_n n 0 (choose n) = 2^n := by
  intro n
  rw [binomial_theorem 1 1]
  conv => rhs; arg 3; intro k;
          rw [one_pow, one_pow]
          simp
  done
