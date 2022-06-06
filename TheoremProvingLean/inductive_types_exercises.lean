/-
Try defining other operations on the natural numbers, such as multiplication, 
the predecessor function (with pred 0 = 0), truncated subtraction 
(with n - m = 0 when m is greater than or equal to n), and exponentiation. 
Then try proving some of their basic properties, 
building on the theorems we have already proved.

Since many of these are already defined in Lean's core library, 
you should work within a namespace named Hidden, or something like that, 
in order to avoid name clashes.
-/

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

      
    theorem left_mul_cancel (n m k : Nat) : k ≠ zero → m * k = n * k → m = n := by 
      intro hk
      intro he
      admit 

    #check Eq.symm 

  end Nat
end hidden 


/-
Define some operations on lists, like a length function or the reverse function. Prove some properties, such as the following:

a. length (s ++ t) = length s + length t

b. length (reverse t) = length t

c. reverse (reverse t) = t
-/

namespace hidden1

  inductive List (α : Type u) where 
  | nil : List α 
  | cons : α → List α → List α 
  deriving Repr

  namespace List

    def length (as : List α) : Nat :=
      match as with 
      | nil => 0
      | cons a as' => length as' + 1

    def append (as bs : List α) : List α :=
      match as with 
      | nil => bs 
      | cons a as' => cons a (append as' bs)

    notation:66 as:66 "**" bs:67 => append as bs

    theorem nil_append (as : List α) : nil ** as = as := by rfl 

    theorem cons_append (as bs : List α) (a : α) 
        : cons a (as ** bs) = (cons a as) ** bs := by rfl

    theorem append_nil (as : List α) : as ** nil = as := by 
      induction as with 
      | nil => rfl 
      | cons a as ih => calc
        (cons a as) ** nil = cons a (as ** nil) := by simp only [cons_append]
        _ = cons a as := by simp only [ih]

    theorem append_assoc (as bs cs : List α) 
        : (as ** bs) ** cs = as ** (bs ** cs) := by 
      induction as with 
      | nil => rfl 
      | cons a as ih => calc 
        ((cons a as) ** bs) ** cs = (cons a (as ** bs)) ** cs := by simp only [cons_append]
        _ = cons a ((as ** bs) ** cs) := by simp only [cons_append]
        _ = cons a (as ** (bs ** cs)) := by simp only [ih]
        _ = ((cons a as) ** (bs ** cs)) := by simp only [cons_append]

    theorem length_dist (as bs : List α) : length (as ** bs) = length as + length bs := by 
      induction as with 
      | nil => simp [length, nil_append]
      | cons a as ih => calc 
        length ((cons a as) ** bs) = length (cons a (as ** bs)) := by simp only [cons_append]
        _ = length (as ** bs) + 1 := by simp only [length]
        _ = length as + length bs + 1 := by simp only [ih]
        _ = length (cons a as) + length bs := by simp_arith only [length]

    def reverse (as : List α) :=
      match as with 
      | nil => as
      | cons a as' => (reverse as') ** (cons a nil)


    theorem length_reverse (as : List α)
        : length (reverse as) = length as := by 
      induction as with 
      | nil => rfl 
      | cons a as ih => calc 
        length (reverse (cons a as)) = length ((reverse as) ** (cons a nil)) := by simp [reverse]
        _ = length (reverse as) + length (cons a nil) := by simp [length_dist]
        _ = length as + 1 := by simp [length, ih]

    theorem reverse_append (as bs : List α)
        : reverse (as ** bs) = reverse bs ** reverse as := by 
      induction as with 
      | nil => simp [reverse, append_nil]; rfl 
      | cons a as ih => calc 
        reverse ((cons a as) ** bs) = reverse (cons a (as ** bs)) := by 
          simp only [cons_append]
        _ = (reverse (as ** bs)) ** (cons a nil) := by simp [reverse]
        _ = (reverse bs ** reverse as) ** (cons a nil) := by simp [ih]
        _ = reverse bs ** (reverse as ** (cons a nil)) := by simp [append_assoc]
        _ = reverse bs ** reverse (cons a as) := by simp [reverse]

  
    theorem reverse_rev (as : List α) : reverse (reverse as) = as := by 
      induction as with 
      | nil => rfl 
      | cons a as ih => calc 
        reverse (reverse (cons a as)) = reverse ((reverse as) ** (cons a nil)) := by
          simp only [reverse]
        _ = reverse (cons a nil) ** reverse (reverse as) := by simp [reverse_append]
        _ = reverse (cons a nil) ** as := by simp [ih]
        _ = (cons a nil) ** as := by rfl
        _ = cons a as := by rfl
      

  end List


end hidden1