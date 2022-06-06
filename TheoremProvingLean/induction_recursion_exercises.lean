/- Natural Numbers -/

namespace hidden 

  inductive Nat where 
  | zero : Nat 
  | succ : Nat → Nat
  deriving Repr

  namespace Nat 

    /- Addition -/
    def add (m n : Nat) : Nat := 
      match n with 
      | zero => m
      | succ n' => Nat.succ (add m n')
    
    notation:65 lhs:65 "+" rhs:66 => add lhs rhs
    notation:max "one" => succ zero 

    theorem zero_not_succ (n : Nat) : succ n ≠ zero := by simp [add]

    theorem add_zero (n : Nat) : n + zero = n := by rfl 

    theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := by rfl

    theorem succ_eq_add_one (n : Nat) : n + one = succ n := by 
      calc 
        n + one = succ (n + zero) := by simp only [add_succ]
        _ = succ n := by simp only [add_zero]

    theorem zero_add (n: Nat) : zero + n = n := 
      Nat.recOn (motive := fun x => zero + x = x)
        n 
        (show zero + zero = zero from rfl)
        (fun (n : Nat) (ih : zero + n = n) => 
          show zero + succ n = succ n from 
            calc
              zero + succ n = succ (zero + n) := rfl 
              _ = succ n := by rw [ih])

    theorem add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := 
      Nat.recOn (motive := fun x => (m + n) + x = m + (n + x)) k
        (show (m + n) + zero = m + (n + zero) by rfl)
        (fun k ih => by 
          calc 
            (m + n) + succ k = succ ((m + n) + k) := by rfl 
            _ = succ (m + (n + k)) := by rw [ih])

    theorem succ_add (m n : Nat) : succ n + m = succ (n + m) := 
      Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m 
        (by rfl)
        (fun m ih => by simp only [add_succ, *])


    theorem add_comm (m n : Nat) : m + n = n + m := 
      Nat.recOn (motive := fun x => m + x = x + m) n 
        (show m + zero = zero + m by simp [zero_add, add])
        (fun n ih => by calc 
          m + succ n = succ (m + n) := by rfl
          _ = succ (n + m) := by rw [ih]
          _ = succ n + m := by simp only [succ_add]) 

    theorem succ_eq (m n : Nat) : succ m = succ n → m = n := by 
      intro h 
      match h with 
      | rfl => rfl

    theorem left_add_cancel (m n k : Nat) : m + k = n + k → m = n := by 
      intro h 
      induction k with 
      | zero => simp only [add_zero]; assumption
      | succ k ih => 
        have : succ (m + k) = succ (n + k) := by simp only [add]; assumption
        have : m + k = n + k := by apply succ_eq; assumption 
        show m = n; simp only [ih, *]


    theorem not_and_iff_or_not (p q : Prop) : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := by
      apply Iff.intro
      . intro 
        cases (Classical.em p) with 
        | inl => cases (Classical.em q) with 
          | inl => 
            have : p ∧ q := by constructor <;> assumption 
            contradiction
          | inr => apply Or.inr; assumption
        | inr => apply Or.inl; assumption
      . intro h
        intro 
        | And.intro _ _ =>
          cases h <;> contradiction


    theorem zero_sum_elim (m n : Nat) : m + n = zero → m = zero ∧ n = zero := by 
      intro h 
      apply Classical.byContradiction
      intro hn
      have : ¬ (m = zero) ∨ ¬ (n = zero) := Iff.mp (not_and_iff_or_not ..) hn 
      have : m ≠ zero ∨ n ≠ zero := by simp [*]
      cases this with 
      | inl => match m with 
        | zero => contradiction
        | succ m' => 
          have : succ (m' + n) = zero := by simp [succ_add, *] at h 
          match (succ (m' + n)) with 
          | zero => contradiction
          | succ a => contradiction 
      | inr => match n with 
        | zero => contradiction
        | succ n' => 
          have : succ (m + n') = zero := by simp [add, *] at h
          cases (succ (m + n')) <;> contradiction
        

    /- Predecesor -/
    def pred (n : Nat) : Nat := 
      match n with 
      | zero => zero 
      | succ n' => n' 

    theorem succ_pred_self (n : Nat) (h : n ≠ zero) : succ (pred n) = n := 
      match n with 
      | zero => by contradiction 
      | succ n' => by rfl 

    
    /- Multiplication -/
    def mul (m n : Nat) : Nat := 
      match n with 
      | zero => zero 
      | succ n' => mul m n' + m 

    notation:75 lhs:75 "*" rhs:76 => mul lhs rhs
    

    theorem mul_zero (n : Nat) : n * zero = zero := by rfl 

    theorem mul_succ (m n : Nat) : m * succ n = m * n + m := by rfl 

    theorem zero_mul (n : Nat) : zero * n = zero := by 
      induction n with 
      | zero => rfl 
      | succ n ih => calc 
        zero * succ n = zero * n + zero := by rw [mul_succ]
        _ = zero + zero := by simp only [ih]
        _ = zero := by simp only [add]

    theorem mul_one (n : Nat) : n * one = n := by 
      calc
        n * one = n * zero + n := by simp only [mul]
        _ = n := by simp only [mul_zero, zero_add]

    theorem mul_add (m n k : Nat) : m * (n + k) = m * n + m * k := by 
      induction k with 
      | zero => rfl 
      | succ k ih => calc 
        m * (n + succ k) = m * succ (n + k) := by simp only [add]
        _ = m * (n + k) + m := by simp only [mul]
        _ = m * n + m * k + m := by rw [ih]
        _ = m * n + m * succ k := by simp only [mul_succ, add_assoc]

    theorem add_mul (m n k : Nat) : (m + n) * k = m * k + n * k := by 
      induction k with 
      | zero => rfl 
      | succ k ih => calc
        (m + n) * succ k = (m + n) * k + (m + n) := by simp only [mul_succ]
        _ = m * k + n * k + (m + n) := by rw [ih]
        _ = (m * k + m) + (n * k + n) := by simp only [←add_assoc, add_comm]
        _ = m * succ k + n * succ k := by simp only [mul_succ]

    theorem one_mul (n : Nat) : one * n = n := by 
      induction n with 
      | zero => rfl 
      | succ n ih => calc 
        one * succ n = one * n + one := by simp only [mul]
        _ = n + one := by rw [ih]
        _ = succ n := by rw [succ_eq_add_one]

    theorem mul_comm (m n : Nat) : m * n = n * m := by 
      induction n with 
      | zero => simp only [mul_zero, zero_mul]
      | succ n ih => calc 
        m * succ n = m * n + m := by simp only [mul]
        _ = n * m + one * m := by simp only [ih, one_mul]
        _ = (n + one) * m := by simp only [add_mul]
        _ = succ n * m := by simp only [succ_eq_add_one]

    theorem mul_assoc (m n k : Nat) : m * (n * k) = (m * n) * k := by 
      induction k with 
      | zero => simp only [mul]
      | succ k ih => calc 
        m * (n * succ k) = m * (n * k + n) := by simp only [mul]
        _ = m * (n * k) + m * n := by simp only [mul_add]
        _ = (m * n) * k + (m * n) * one := by simp only [ih, mul_one]
        _ = (m * n) * (k + one) := by simp only [mul_add]
        _ = (m * n) * succ k := by simp only [succ_eq_add_one]

    theorem not_or_iff_and_not (p q : Prop) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by 
      apply Iff.intro 
      . intro 
        cases (Classical.em p) with 
        | inl =>
          have : p ∨ q := by apply Or.inl; assumption
          contradiction
        | inr => cases (Classical.em q) with 
          | inl => 
            have : p ∨ q := by apply Or.inr; assumption
            contradiction
          | inr => constructor <;> assumption
      . intro h
        intro ho  
        cases ho with 
        | inl => apply h.left; assumption 
        | inr => apply h.right; assumption

    theorem zero_mul_elim (m n : Nat) : zero = m * n → m = zero ∨ n = zero := by 
      intro h
      apply Classical.byContradiction
      intro 
      have : m ≠ zero ∧ n ≠ zero := by 
        apply Iff.mp (not_or_iff_and_not ..); assumption
      match this with 
      | And.intro _ _ =>
        match n with 
        | zero => contradiction
        | succ n => match m with 
          | zero => contradiction
          | succ m => 
            have : zero = succ (succ m * n + m) := by calc 
              zero = succ m * succ n := by simp only [*]
              _ = succ m * n + succ m := by simp only [mul]
              _ = succ (succ m * n + m) := by simp only [add]
            contradiction

    /-
    Exponentiation of Natural Numbers
    -/

    def pow : Nat → Nat → Nat 
      | zero, zero => zero
      | _, zero => one 
      | m, succ n => (pow m n) * m

    notation:85 lhs:85 "^" rhs:86 => pow lhs rhs

    theorem pow_zero (n : Nat) : n ≠ zero → n ^ zero = one := by 
      intro; cases n; contradiction; rfl


    theorem pow_one (n : Nat) : n ^ one = n := by
      match n with 
      | zero => rfl 
      | succ n => calc 
        (succ n) ^ one = (succ n) ^ zero * (succ n) := by simp only [pow]
        _ = one * (succ n) := by simp only [pow]
        _ = succ n := by simp only [one_mul]

    theorem one_pow (n : Nat) : one ^ n = one := by 
      induction n with 
      | zero => rfl 
      | succ n ih => simp [pow, ih, one_mul]

    theorem zero_pow (n : Nat) : zero ^ n = zero := by 
      cases n <;> rfl

    theorem pow_mul_sum (n a b : Nat) : n ^ a * n ^ b = n ^ (a + b) := by 
      induction a with 
      | zero => match n with 
        | zero => calc
          zero ^ zero * zero ^ b = zero * zero ^ b := by simp [pow]
          _ = zero ^ (zero + b) := by simp [zero_mul, zero_pow, zero_add]
        | succ n => 
          have : succ n ≠ zero := by simp [add]
          calc
            succ n ^ zero * succ n ^ b = one * succ n ^ b := by simp [pow_zero (succ n) this]
            _ = succ n ^ b := by simp [one_mul]
            _ = succ n ^ (zero + b) := by simp [zero_add]
      | succ a ha => calc 
        n ^ (succ a) * n ^ b = (n ^ a * n) * n ^ b := by simp [pow]
        _ = (n ^ a * n ^ b) * n := by simp [mul_assoc, mul_comm]
        _ = n ^ (a + b) * n := by rw [ha]
        _ = n ^ (succ (a + b)) := by simp [pow]
        _ = n ^ ((a + one) + b) := by simp [succ_eq_add_one (a + b), add_assoc, add_comm]; rfl
        _ = n ^ (succ a + b) := by simp [succ_eq_add_one]

    theorem pow_dist (m n a : Nat) : (m * n) ^ a = m ^ a * n ^ a := by 
      induction a with 
      | zero => match m, n with 
        | zero, _ => simp [zero_mul, pow]
        | _, zero => simp [mul_zero, pow]
        | succ m, succ n => simp [pow]; rfl
      | succ a ih => calc 
         (m * n) ^ (succ a) = (m * n) ^ a * (m * n) := by simp [pow]
         _ = (m ^ a * n ^ a) * (m * n) := by rw [ih]
         _ = (m ^ a * m) * (n ^ a * n) := by simp [mul_comm, mul_assoc]
         _ = m ^ succ a * n ^ succ a := by simp [pow]

    theorem pow_of_pow (n a b : Nat) : (n ^ a) ^ b = n ^ (a * b) := by 
      induction a with
      | zero => match n with
        | zero => simp [pow, zero_pow]
        | succ n => calc 
          (succ n ^ zero) ^ b = one ^ b := by simp [pow_zero]
          _ = one ^ (zero * b) := by simp [one_pow]
          _ = (succ n) ^ (zero * b) := by simp [pow_zero, zero_mul]
      | succ a ih => calc 
        (n ^ (succ a)) ^ b = (n ^ a * n) ^ b := by simp [pow]
        _ = (n ^ a) ^ b * n ^ b := by simp [pow_dist]
        _ = n ^ (a * b) * n ^ b := by simp [ih]
        _ = n ^ (a * b + b) := by simp [pow_mul_sum]
        _ = n ^ ((a + one) * b) := by simp [add_mul, one_mul]

    /- Nth root of b eq a -/
    def root (n b a : Nat) : Prop := a ^ n = b

    theorem root_cancel : root n (b ^ n) b := by rfl
  end Nat
end hidden

/- Operation over Vectors -/

namespace hidden2 

  inductive Vector (α : Type u) : Nat → Type u where 
  | nil : Vector α 0 
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)
  deriving Repr

  namespace Vector

  def head : {n : Nat} → Vector α (n + 1) → α 
    | _, cons a as => a 

  def tail : {n : Nat} → Vector α (n + 1) → Vector α n
    | _, cons a as => as

  def appendAux (h : m = n) (vs : Vector α m) : Vector α n := by 
    simp [h] at vs; assumption


  def append {m n : Nat} (as : Vector α m) (bs : Vector α n) : Vector α (m + n) := by
    match m, as with 
    | 0, nil => 
      have : n = 0 + n := by simp_arith
      exact appendAux this bs
    | Nat.succ m, cons a as =>
      have : (m + (n + 1) = (m + 1) + n) := by simp_arith [←Nat.add_assoc m 1 n]
      exact appendAux this (cons a (append as bs)) 

  #eval append (cons 1 (cons 2 nil)) (cons 4 (cons 5 nil)) -- 1 2 4 5

  end Vector

end hidden2


/- Arithmetic Operations -/

inductive Expr where
| const : Nat → Expr
| var : Nat → Expr 
| plus : Expr → Expr → Expr 
| times : Expr → Expr → Expr 
deriving Repr

namespace Expr

  def sampleExpr : Expr := 
    plus (times (var 0) (const 7)) (times (const 2) (var 1))

  def eval (v : Nat → Nat) : Expr → Nat 
    | const n => n 
    | var n => v n 
    | plus e f => (eval v e) + (eval v f)
    | times e f => (eval v e) * (eval v f)

  def sampleVal : Nat → Nat 
    | 0 => 5
    | 1 => 6 
    | _ => 0

  #eval eval sampleVal sampleExpr -- 47 

  def simpConst : Expr → Expr 
    | plus (const a) (const b) => const (a + b)
    | times (const a) (const b) => const (a * b)
    | e => e


  theorem simpConst_eq (v : Nat → Nat) 
      : ∀ e : Expr, eval v (simpConst e) = eval v e := by 
    intro e
    match e with 
    | const n => rfl 
    | var n => rfl 
    | plus f g => admit 
    | times f g => match f, g with 
      | const m, const n => rfl 
      | f, g => admit



end Expr

