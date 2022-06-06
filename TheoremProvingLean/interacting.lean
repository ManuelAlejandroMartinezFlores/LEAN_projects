/- More on Sections -/

namespace ms 
  section 
    variable (x y : Nat)

    def double := x + x

    #check double (x + 1)

    theorem t1 : double (x + y) = double x + double y := by
      simp_arith [double]

    #check t1 y 1

    theorem t2 : double (x * y) = double x * y := by 
      simp_arith [double, Nat.add_mul]

  end
end ms


/- Attributes -/

namespace att 
  def isPrefix (l₁ l₂ : List α) : Prop := ∃ t, l₁ ++ t = l₂
  /- 
  @[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
    Exists.intro [] (by simp)
  -/

  instance : LE (List α) where le := isPrefix 

  @[simp] theorem List.isPrefix_self (as : List α) : as ≤ as :=  
    Exists.intro [] (by simp)

  example : [1, 2] ≤ [1, 2] := by simp 
end att


/- More on Implicit Arguments -/

namespace mia 
  def f (x : Nat) {y : Nat} (z : Nat) := x + z
  #check f 7 -- Nat → Nat
  #check f 7 3 -- Nat

  def f' (x : Nat) ⦃y : Nat⦄ (z : Nat) := x + z
  #check f' 7 -- ⦃Nat⦄ Nat → Nat  f
  #check f' 7 3 -- Nat

  def reflexive {α : Type u} (r : α → α → Prop) : Prop := 
    ∀ {{a}}, r a a

  def symmetric {α : Type u} (r : α → α → Prop) : Prop := 
    ∀ {{a b}}, r a b → r b a 

  def transitive {α : Type u} (r : α → α → Prop) : Prop := 
    ∀ {{a b c}}, r a b → r b c → r a c 

  def euclidean {α : Type u} (r : α → α → Prop) : Prop := 
    ∀ {{a b c}}, r a b → r a c → r b c

  theorem th1 {α : Type u} {r : α → α → Prop}
      (reflr : reflexive r) (eucl : euclidean r) : symmetric r := by
    repeat intro
    apply eucl; assumption
    apply reflr

  theorem th2 {α : Type u} {r : α → α → Prop}
      (symm : symmetric r) (eucl : euclidean r) : transitive r := by 
    repeat intro 
    apply eucl
    apply symm 
    repeat assumption

  theorem th3 {α : Type u} {r : α → α → Prop}
      (reflr : reflexive r) (eucl : euclidean r) : transitive r := by
    repeat intro 
    have : symmetric r := by apply th1 <;> assumption 
    apply th2 <;> assumption 
end mia

/- Notation -/
/-
namespace not 
  infixl:65 "+" => HAdd.hAdd
  infix:50 "=" => Eq 
  set_option quotPrecheck false
  postfix:max "⁻¹" => Inv.inv

  notation:65 lhs:65 "+" rhs:66 => HAdd.hAdd lhs rhs -- a + b + c = (a + b) + c
  notation:80 base:81 "^" exp:80 => HPow.hPow base exp -- a ^ b ^ c = a ^ (b ^ c)
end not
-/

/- Coercions -/

namespace coer
  variable (m n : Nat) (i j : Int)
  #check i + m -- i + Int.ofNat m : Int
  #check m + i -- Int.ofNat m + i : Int
end coer 

/- Options -/

namespace opt 
  /-
    pp.explicit  : display implicit arguments
    pp.universes : display hidden universe parameters
    pp.notation  : display output using defined notations
  -/

  set_option pp.explicit true
  set_option pp.universes true 
  set_option pp.notation false 
  /-
  #check 2 + 2 = 4
  #reduce (fun x => x + 2) = (fun x => x + 3)
  #check (fun x => x + 1) 1
  -/
end opt 


/- AutoBound Implicit Arguments -/

namespace abia 
  section
    universe u v w 
    def compose₀ {α : Type u} {β : Type v} {γ : Type w}
        (g : β → γ) (f : α → β) (x : α) : γ :=
      g (f x)
  end

  def compose₁.{u, v, w}
      {α : Type u} {β : Type v} {γ : Type w}
      (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

  def compose (g : β → γ) (f : α → β) (x : α) : γ := 
    g (f x)

  /-
  @compose : {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
  -/
  #check @compose


end abia 


/- Sugar for Simple Functions -/

namespace Sugar 
  #check (2 - ·) -- fun a => 2 - a

  #eval [1, 2, 3, 4, 5].foldl (· * ·) 1 -- 120 

  #eval [(1, 2), (3, 4), (5, 6)].map (·.1) -- [1, 3, 5]
end Sugar

/- Named Arguments -/

namespace na 
  def sum (xs : List Nat) : Nat := 
    xs.foldl (init:=0) (Nat.add · ·)
  #eval sum [1, 2, 3, 4] -- 10

  example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
      : p a a b :=
    Eq.subst (motive := fun x => p a x b) h₂ h₁

  def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
    match b? with 
    | none => a + c 
    | some b => a + b + c

  variable {α} [Add α]
  example (x : α) : g (c := x) = fun (a : α) => a + x := rfl 

  

end na 