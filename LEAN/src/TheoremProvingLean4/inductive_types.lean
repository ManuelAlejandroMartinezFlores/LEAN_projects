/- Inductive Type 

    inductive Foo where
      | constructor₁ : ... → Foo
      | constructor₂ : ... → Foo
      ...
      | constructorₙ : ... → Foo
-/

/- Enumerated Types -/

namespace ent 
  inductive Weekday where 
  | monday :  Weekday
  | tuesday : Weekday 
  deriving Repr 

  #eval Weekday.monday

  #check Weekday.monday 

  def Weekday.numerOfDay (d : Weekday) : Nat := 
    match d with 
    | monday => 1 
    | tuesday => 2
  
  #eval Weekday.monday.numerOfDay -- 1

  def Weekday.next (d : Weekday) : Weekday := 
    match d with 
    | monday => tuesday
    | tuesday => monday

  def Weekday.prev (d : Weekday) : Weekday := 
    match d with 
    | monday => tuesday
    | tuesday => monday

  example (d : Weekday) : d.next.prev = d := by 
    cases d <;> rfl 

  namespace hidden
    inductive Bool where
    | True 
    | False 
    deriving Repr

    def Bool.and (p q : Bool) : Bool :=
      match p with 
      | True => q 
      | False => False 

    #eval Bool.and Bool.True Bool.False -- False
    #eval Bool.and Bool.True Bool.True -- True

    def Bool.or (p q : Bool) : Bool := 
      match p with 
      | True => True 
      | False => q

    #eval Bool.or Bool.True Bool.False -- True
    #eval Bool.or Bool.True Bool.True -- True
    #eval Bool.or Bool.False Bool.False -- True

    def Bool.not (p : Bool) : Bool :=
      match p with
      | True => False 
      | False => True

    #eval Bool.not Bool.True -- False

  end hidden

end ent


/- Constructors w Arguments -/

namespace cwa 
  namespace hidden
    inductive Prod (α : Type u) (β : Type v) 
    | mk : α → β → Prod α β 

    inductive Sum (α : Type u) (β : Type v) where 
    | inl : α → Sum α β 
    | inr : β → Sum α β 

    def fst {α : Type u} {β : Type v} (p : Prod α β) : α := 
      match p with 
      | Prod.mk a b => a 

    def snd {α : Type u} {β : Type v} (p : Prod α β) : β := 
      match p with 
      | Prod.mk a b => b 
  end hidden

  def prod_example (p : Bool × Nat) : Nat := 
    Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2*n) (2*n+1))

  #eval prod_example (true, 3) -- 6 
  #eval prod_example (false, 1) -- 3

  def sum_example (s : Sum Nat Nat) : Nat := 
    Sum.casesOn (motive := fun _ => Nat) s
      (fun n => 2 * n)
      (fun n => 2 * n + 1)

  #eval sum_example (Sum.inl 3) -- 6 
  #eval sum_example (Sum.inr 3) -- 7


  structure Semigroup where 
    carrier : Type u 
    mul : carrier → carrier → carrier 
    mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

  namespace hidden 
    inductive Sigma {α : Type u} (β : α → Type v) where 
    | mk : (a : α) → β a → Sigma β 

    inductive Option (α : Type u) where 
    | none : Option α 
    | some : α → Option α 

    inductive Inhabited (α : Type u) where 
    | mk : α → Inhabited α 
  end hidden
end cwa

/- Inductively Defined Prop -/

namespace idp 
  namespace hidden 
    inductive False : Prop 

    inductive True : Prop where 
    | intro : True 

    inductive And (p q : Prop) : Prop where 
    | intro : p → q → And p q 

    inductive Or (p q : Prop) : Prop where 
    | inl : p → Or p q 
    | inr : q → Or p q 

    inductive Exists {α : Type u} (p : α → Prop) where 
    | intro : ∀ (a : α), p a → Exists p 
  end hidden
end idp 


/- Defining Natural Numbers -/

namespace dnn 
  namespace hidden 
    inductive Nat where 
    | zero : Nat 
    | succ : Nat → Nat
    deriving Repr

    /-
    @Nat.rec : {motive : Nat → Sort u_1} →
      motive Nat.zero → ((a : Nat) → motive a → motive (Nat.succ a)) → (t : Nat) → motive t
    -/
    #check @Nat.rec 

    /-
    @Nat.recOn :
      {motive : Nat → Sort u}
      → (t : Nat)
      → motive Nat.zero
      → ((n : Nat) → motive n → motive (Nat.succ n))
      → motive t
    -/

    def Nat.add (m n : Nat) : Nat := 
      match n with 
      | zero => m
      | succ n' => Nat.succ (add m n')

    #eval Nat.add (Nat.succ Nat.zero) Nat.zero -- succ zero
    #eval Nat.add (Nat.succ Nat.zero) (Nat.succ Nat.zero) -- succ (succ zero)
  end hidden

  namespace hidden2
    open Nat 
    theorem zero_add (n: Nat) : 0 + n = n := 
      Nat.recOn (motive := fun x => 0 + x = x)
        n 
        (show 0 + 0 = 0 from rfl)
        (fun (n : Nat) (ih : 0 + n = n) => 
          show 0 + succ n = succ n from 
            calc
              0 + succ n = succ (0 + n) := rfl 
              _ = succ n := by rw [ih])

    theorem zero_add₁ (n: Nat) : 0 + n = n := 
      Nat.recOn (motive:= fun x => 0 + x = x) n
        (by rfl)
        (fun n ih => by simp only [add_succ, *])

    theorem add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := 
      Nat.recOn (motive := fun x => (m + n) + x = m + (n + x)) k
        (show (m + n) + 0 = m + (n + 0) by rfl)
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
        (by simp [zero_add])
        (fun n ih => by calc 
          m + succ n = succ (m + n) := by rfl
          _ = succ (n + m) := by rw [ih]
          _ = succ n + m := by simp only [succ_add]) 
  end hidden2
end dnn

/- Other Recursive Data Types -/

namespace ordt 
  namespace hidden 
    /- List -/
    inductive List (α : Type u) where 
    | nil : List α 
    | cons : α → List α → List α 

    def List.append (as bs : List α) : List α := 
    match as with
    | nil => bs 
    | cons a as' => cons a (append as' bs) 

    theorem List.nil_append (as : List α) : List.append List.nil as = as := 
      by rfl 

    theorem List.cons_append (a : α) (as bs : List α) 
        : cons a (append as bs) = append (cons a as) bs :=
      by rfl 

    theorem List.append_nil (as : List α) : append as nil = as := 
      List.recOn (motive := fun x => append x nil = x) as 
        (by rfl)
        (fun a as ih => by calc 
          append (cons a as) nil = cons a (append as nil) := by simp only [cons_append]
          _ = cons a as := by rw [ih])

    theorem List.append_assoc (as bs cs : List α) 
        : append (append as bs) cs = append as (append bs cs) := 
      List.recOn (motive := fun x => append (append x bs) cs = append x (append bs cs)) as 
        (by rfl)
        (fun a as ih => by calc 
          append (append (cons a as) bs) cs = append (cons a (append as bs)) cs := by 
            simp only [cons_append]
          _ = cons a (append (append as bs) cs) := by simp only [cons_append]
          _ = cons a (append as (append bs cs)) := by simp [ih]
          _ = append (cons a as) (append bs cs) := by simp only [cons_append])


    def List.length (as : List α) : Nat := 
      match as with 
      | nil => 0 
      | cons a as' => Nat.succ (length as')

    theorem List.length_assoc (as bs : List α) 
        : length (append as bs) = length as + length bs := 
      List.recOn
        (motive := fun x => length (append x bs) = length x + length bs)
        as 
        (by simp only [length, nil_append, Nat.zero_add])
        (fun a as ih => by calc 
          length (append (cons a as) bs) = length (cons a (append as bs)) := by
            simp only [cons_append]
          _ = Nat.succ (length (append as bs)) := by simp only [length]
          _ = Nat.succ (length as + length bs) := by rw [ih]
          _ = Nat.succ (length as) + length bs := by simp_arith
          _ = length (cons a as) + length bs := by simp only [length])

    
    /- Binary Trees -/
    inductive BinaryTree where 
    | leaf : BinaryTree
    | node : BinaryTree → BinaryTree → BinaryTree 

    inductive CBTree where 
    | leaf : CBTree
    | sup : (Nat → CBTree) → CBTree 

    def CBTree.succ (t : CBTree) : CBTree := 
      sup (fun _ => t)
    
    def CBTree.toCBTree : Nat → CBTree
      | 0 => leaf 
      | n + 1 => succ (toCBTree n)

  end hidden
end ordt 


/- Tactics for Inductive Types -/

namespace tfit 
  example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by 
    intro n 
    cases n
    . assumption
    . apply hs

  example (n : Nat) (h : n ≠ 0) : Nat.succ (Nat.pred n) = n := by 
    cases n with 
    | zero => contradiction
    | succ n' => rfl 

  example (p : Prop) (m n : Nat) (h1 : m < n → p) (h2 : m ≥ n → p) : p := by 
    cases Nat.lt_or_ge m n 
    . case inl => apply h1; assumption
    . case inr => apply h2; assumption

  example (m n : Nat) : m - n = 0 ∨ m ≠ n := by 
    cases Decidable.em (m = n) with 
    | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
    | inr => apply Or.inr; assumption 

  namespace hidden 
    open Nat
    theorem zero_add (n : Nat) : 0 + n = n := by 
      induction n with
      | zero => rfl 
      | succ n' ih => rw [add_succ, ih] 
  end hidden

  /-
  theorem Nat.mod.inductionOn
        {motive : Nat → Nat → Sort u}
        (x y  : Nat)
        (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
        (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
        : motive x y :=
  -/
  #check @Nat.mod_eq_sub_mod
  example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by 
    induction x, y using Nat.mod.inductionOn with 
    | ind x y h1 ih => 
      rw [Nat.mod_eq_sub_mod h1.right]
      exact ih h 
    | base x y h1 =>
      have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h1
      match this with 
      | Or.inl _ => contradiction
      | Or.inr _ => 
        have : y > x := by apply Nat.gt_of_not_le; assumption 
        rw [← Nat.mod_eq_of_lt this] at this
        assumption

  example :
      (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
      =
      (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
    funext (a, b) (c, d)
    show a + d = d + a
    rw [Nat.add_comm]

  example (m n k : Nat) (h : m.succ.succ = n.succ.succ)
      : n + k = m + k := by 
    injection h with h' -- m.succ = n.succ
    injection h' with h'' -- m = n
    rw [h'']

  namespace hidden 
    inductive Vector (α : Type u) : Nat → Type u where 
    | nil : Vector α 0
    | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)
    deriving Repr

    #eval Vector.cons 1 (Vector.nil)

    inductive Eq {α : Sort u} (a : α) : α → Prop where 
    | refl {} : Eq a a

    /-
    @Eq.recOn : {α : Sort u_2} →
      {a : α} →
        {motive : (a_1 : α) → Eq a a_1 → Sort u_1} → {a_1 : α} → (t : Eq a a_1) → motive a (_ : Eq a a) → motive a_1 t
    -/
    #check @Eq.recOn


    /-
    @Eq.rec : {α : Sort u_2} →
      {a : α} →
        {motive : (a_1 : α) → Eq a a_1 → Sort u_1} → motive a (_ : Eq a a) → {a_1 : α} → (t : Eq a a_1) → motive a_1 t
    -/
    #check @Eq.rec 

    theorem Eq.subst {α : Type u} {a b : α} {p : α → Prop} 
        (h1 : Eq a b) (h2 : p a) : p b := 
      Eq.rec (motive := fun x _ => p x) h2 h1 

    theorem Eq.subst₁ {α : Type u} {a b : α} {p : α → Prop} 
        (h1 : Eq a b) (h2 : p a) : p b := 
      match h1 with 
      | refl a => h2

    theorem Eq.symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a := 
      match h with 
      | refl a => refl a

    theorem Eq.trans {α : Type u} {a b c : α} (h1 : Eq a b) (h2 : Eq b c)
        : Eq a c := 
      match h1, h2 with 
      | refl a, refl a => refl a

    theorem Eq.congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b)
        : Eq (f a) (f b) := 
      match h with 
      | refl a => refl (f a) 
  end hidden 
end tfit


/- Mutual and Nested Inductive Types -/

namespace munit 

  mutual  
    inductive Even : Nat → Prop where 
    | even_zero : Even 0 
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

    inductive Odd : Nat → Prop where 
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
  end 

  inductive Tree (α : Type u) where 
  | mk : α → List (Tree α) → Tree α 
end munit 