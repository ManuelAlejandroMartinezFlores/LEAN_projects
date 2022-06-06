/- Pattern Matching -/

namespace patm

  open Nat

  def sub1 : Nat → Nat
    | zero => zero 
    | succ x => x 

  def isZero : Nat → Bool 
    | 0 => true 
    | x + 1 => false 

  def swap : α × β → β × α 
    | (a, b) => (b, a)

  def bar : Option Nat → Nat 
    | none => 0 
    | some n => n + 1

  def not : Bool → Bool 
    | true => false 
    | false => true 

  theorem not_not : ∀ (b : Bool), not (not b) = b 
    | true => by rfl 
    | false => by rfl 

  def sub2 : Nat → Nat 
    | 0 => 0 
    | 1 => 0 
    | x + 2 => x 

  example (p q : α → Prop)
      : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
    | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
    | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

  def foo : Nat → Nat → Nat
    | 0,   n   => 0
    | m+1, 0   => 1
    | m+1, n+1 => 2

  def bar1 : List Nat → List Nat → Nat
    | [],      []      => 0
    | a :: as, []      => a
    | [],      b :: bs => b
    | a :: as, b :: bs => a + b

  def and : Bool → Bool → Bool 
    | true, b => b 
    | false, _ => false 

  def or : Bool → Bool → Bool 
    | true, _ => true 
    | false, b => b 

  def cond : Bool → α → α → α  
    | true, x, _ => x 
    | false, _, y => y 

end patm


/- Wildcards and Overlapping Patterns -/

namespace wop 

  def foo : Nat → Nat → Nat 
    | 0, _ => 0
    | _, 0 => 1 
    | _, _ => 2 


  def f1 : Nat → Nat → Nat 
    | 0, _ => 1 
    | _, 0 => 2 
    | _, _ => default 

end wop


/- Structural Recursion and Induction -/

namespace sri 
  
  namespace hidden
    open Nat 

    def add : Nat → Nat → Nat 
      | m, zero => m 
      | m, succ n => succ (add m n)

    theorem zero_add : ∀ n, add zero n = n 
      | zero => by rfl 
      | succ n => congrArg succ (zero_add n)
  end hidden

  def fib : Nat → Nat 
    | 0 => 1 
    | 1 => 1
    | n + 2 => fib (n + 1) + fib n

  def fibFast (n: Nat) : Nat := 
    (loop n).1
    where
      loop : Nat → Nat × Nat 
        | 0 => (0, 1)
        | n + 1 => let p := loop n; (p.2, p.1 + p.2)

  
  #eval fibFast 100


  def List.listAdd [Add α] : List α → List α → List α 
    | [], _ => []
    | _, [] => []
    | a :: as, b :: bs => (a + b) :: listAdd as bs 

  #eval List.listAdd [1, 2, 3] [4, 5, 6, 7] -- [5, 7, 9]

end sri


/- Local Recursive Generators -/ 

namespace lrg

  def replicate (n : Nat) (a : α) : List α :=
    let rec loop : Nat → List α → List α 
    | 0, as => as
    | n + 1, as => loop n (a :: as)
    loop n []

  /-
  @replicate.loop : {α : Type u_1} → α → Nat → List α → List α
  -/
  #check @replicate.loop 

  /-
  [4, 4, 4, 4, 4]
  -/
  #eval replicate 5 4

  theorem length_rep (n : Nat) (a : α) : (replicate n a).length = n := by 
    let rec aux (n : Nat) (as : List α)
        : (replicate.loop a n as).length = n + as.length := by 
      match n with
      | 0 => simp [replicate.loop] 
      | n + 1 => simp_arith [replicate.loop, aux]
    exact aux n []

end lrg


/- Well Founded Recursion and Induction -/

namespace wfri 
  
  variable (α : Sort u)
  variable (r : α → α → Prop)

  #check (Acc r : α → Prop) -- ∀ y, r y x → Acc r y
  #check (WellFounded r : Prop)

  namespace hidden


    def div (x y : Nat) : Nat :=  
      if h : 0 < y ∧ y ≤ x then 
        have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
        div (x - y) y + 1
      else 
        0

    #eval div 9 4 -- 2

    example (x y : Nat) 
        : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
      conv => lhs; unfold div 

    example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
      conv => lhs; unfold div; simp [h]

    def natToBin : Nat → List Nat 
      | 0 => [0]
      | 1 => [1]
      | n + 2 =>
        have : (n + 2) / 2 < (n + 2) := sorry 
        natToBin ((n + 2) / 2) ++ [n % 2]

    #eval natToBin 45 -- [1, 0, 1, 1, 0, 1]

    def ack : Nat → Nat → Nat 
      | 0, n => n + 1
      | m + 1, 0 => ack m 1
      | m + 1, n + 1 => ack m (ack (m + 1) n) 
      termination_by ack x y => (x, y)

  end hidden

end wfri 


/- Mutual Recursion -/

namespace mr 

  mutual 
    def even : Nat → Bool 
      | 0 => true 
      | n + 1 => odd n

    def odd : Nat → Bool 
      | 0 => false 
      | n + 1 => even n 
  end 

  theorem even_eq_not_odd : ∀ n, even n = not (odd n) := by 
    intro n; induction n
    . simp [even, odd]
    . simp [even, odd, *]

  mutual  
    inductive Even : Nat → Prop where
    | even_zero : Even 0 
    | even_succ : ∀ n, Odd n → Even (n + 1)

    inductive Odd : Nat → Prop where 
    | odd_succ : ∀ n, Even n → Odd (n + 1)
  end

  open Even Odd
    theorem zero_not_odd : ¬ Odd 0 := by 
      intro; contradiction 

    theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n 
      | _, odd_succ n h => h 

    
  inductive Term where 
  | const : String → Term 
  | app : String → List Term → Term

  namespace Term 

    mutual 
      def numConsts : Term → Nat 
        | const _ => 1 
        | app _ cs => numConstsLst cs

      def numConstsLst : List Term → Nat 
        | [] => 0
        | c :: cs => numConsts c + numConstsLst cs 
    end

    def sample := app "f" [app "g" [const "x"], const "y"]

    #eval numConsts sample -- 2


    mutual 
      def replaceConst (a b : String) : Term → Term 
        | const c => if a == c then const b else const c 
        | app c cs => app c (replaceConstLst a b cs)

      def replaceConstLst (a b : String) : List Term → List Term
        | [] => []
        | c :: cs => replaceConst a b c :: replaceConstLst a b cs
    end

    mutual
      theorem numConsts_replaceConst (a b : String) (e : Term)  
          : numConsts (replaceConst a b e) = numConsts e := by
        match e with 
        | const c => simp [replaceConst]; split <;> simp [numConsts] 
        | app c cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

      theorem numConsts_replaceConstLst (a b : String) (es : List Term)
          : numConstsLst (replaceConstLst a b es) = numConstsLst es := by 
        match es with 
        | [] => simp [replaceConstLst, numConstsLst] 
        | c :: cs => 
          simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
    end

  end Term
end mr


/- Dependent Pattern Matching -/

namespace dpm 

  inductive Vector (α : Type u) : Nat → Type u where 
  | nil : Vector α 0 
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

  namespace Vector
    def tailAux (v : Vector α m) : m = n + 1 → Vector α n := 
      Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
        (fun h : 0 = n + 1 => Nat.noConfusion h)
        (fun (a : α) (m : Nat) (as : Vector α m) =>
          fun (h : m + 1 = n + 1) => 
            Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

    def tail1 (v : Vector α (n + 1)) : Vector α n := 
      tailAux v rfl 

    def head : {n : Nat} → Vector α (n + 1) → α 
      | n, cons a as => a 

    def tail : {n : Nat} → Vector α (n + 1) → Vector α n 
      | n, cons a as => as 

    theorem eta : ∀ {n : Nat} (v : Vector α (n + 1)), cons (head v) (tail v) = v 
      | n, cons a as => by rfl 

    def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
      | 0, nil, nil => nil
      | n + 1, cons a as, cons b bs => cons (f a b) (map f as bs)

    def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
      | 0, nil, nil => nil 
      | n + 1, cons a as, cons b bs => cons (a, b) (zip as bs)

    #print map.match_1

  end Vector

end dpm


/- Inaccesible Patterns -/

namespace ip 

  inductive Vector (α : Type u) : Nat → Type u where 
  | nil : Vector α 0 
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

  namespace Vector 
    def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
      | 0, _, _ => nil 
      | n + 1, cons a as, cons b bs => cons (a + b) (add as bs)

    def add' [Add α] : Vector α n → Vector α n → Vector α n
      | nil,       nil       => nil
      | cons a as, cons b bs => cons (a + b) (add as bs)
  end Vector

end ip

/- Match Expressions -/


namespace me 

  def isNotZero : Nat → Bool 
    | 0 => false 
    | n + 1 => true

  def filter (p : α → Bool) : List α → List α 
    | [] => []
    | a :: as =>
      match p a with 
      | true => a :: (filter p as)
      | false => filter p as

  example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := by rfl 

  def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

  def bar₂ (p : Nat × Nat) : Nat :=
    match p with
    | (m, n) => m + n

  def bar₃ : Nat × Nat → Nat :=
    fun (m, n) => m + n

  def bar₄ (p : Nat × Nat) : Nat :=
    let (m, n) := p; m + n

end me