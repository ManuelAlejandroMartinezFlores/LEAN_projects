/- constants -/
section constants
  def m : Nat := 1  -- natural 
  def n : Nat := 0
  def b1 : Bool := true -- boolean
  def b2 : Bool := false
end constants


/- check types -/

section check_types
  #check m
  #check n
  #check n + 0
  #check m * (n + 0)
  #check b1
  #check b1 && b2 -- && is and
  #check b1 || b2 -- || is or
  #check true
end check_types


/- Evaluate -/

section evaluate
  #eval 4 * 5
  #eval m + 2
  #eval b1 && b2
end evaluate


/-**************************************-/

/- functions from Nat to Nat-/
#check Nat → Nat -- use "\to" or "\r"
#check Nat -> Nat 

/- cartesian product -/
#check Nat × Nat -- use "\times"
#check Prod Nat Nat

/- functions -/
#check Nat → Nat → Nat
#check Nat → (Nat → Nat) -- the same

#check (Nat → Nat) → Nat -- "functional"
#check (Nat × Nat) → Nat

#check Nat.succ -- Nat → Nat
#check (0, 1) -- Nat × Nat
#check Nat.add -- Nat → Nat → Nat
#check Nat.add 3 -- Nat → Nat

#eval Nat.succ 2 -- 3
#eval Nat.add 3 1 -- 4
#eval (5, 9).1 -- 5
#eval (5, 9).2 -- 9
#check ((5, 4), 3) -- (Nat × Nat) × Nat
#check (5, (4, 3)) -- Nat × Nat × Nat
#eval ((5, 4), 3).1 -- (5, 4)
#eval (5, (4, 3)).1 -- 5



/- types -/

section types
  def α : Type := Nat
  def β : Type := Bool
  def F : Type → Type := List
  def G : Type → Type → Type := Prod

  #check α -- Type
  #check F α -- Type
  #check G α -- Type → Type
  #check G α β -- Type
  #check List α -- Type

  #check Type -- Type 1
  #check Type 1 -- Type 2 (Type n is a Type (n+1))

  #check List -- Type u_1 → Type u_1
  #check Prod -- Type u_1 → Type u_2 → Type (max u_1 u_2)
end types


/- function abstraction -/
section abstraction
  #check fun (x : Nat) => x + 5
  #check λ (x : Nat) => x + 5
  #eval (λ x : Nat => x + 5) 10 -- 15

  #check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
  #check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
  #check fun x y => if not y then x + 1 else x + 2
  #eval (fun x y => if not y then x + 1 else x + 2) 1 true -- 3

  def f (n : Nat) : String := toString n
  def g (s : String) : Bool := s.length > 0
  #eval f 10 -- "10"
  #eval g "abc" -- false
  #check fun x: Nat => x
  #check fun x : Nat => true
  #check fun x : Nat => g (f x)
  #eval (fun x => g (f x)) 10 -- true

  #check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

  #check (fun x : Nat => x) 1 -- Nat
  #check (fun x : Nat => true) 1 -- Bool

  def a (n : Nat) : String := toString n
  def b (s : String) : Bool := s.length > 0
  #check (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool b a 0 -- Bool
end abstraction


/- Definitions -/

section definitions

  def double (x : Nat) : Nat :=
    x + x

  #eval double 3 -- 6

  def add (x y : Nat) : Nat :=
    x + y

  #eval add 3 5 -- 8
  #eval add (double 3) (add 3 5) -- 14

  def greater (x y : Nat) : Nat :=
    if x > y then x
    else y

  #eval greater 3 5 -- 5


  def doTwice (f : Nat → Nat) (x : Nat) :=
    f (f x)

  #eval doTwice double 3 -- 12


  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

  def square (x : Nat) : Nat :=
    x * x

  #eval compose Nat Nat Nat double square 3 -- 18

end definitions
/- Local Definitions -/

section local_definitions
  #check let y := 2 + 2; y * y -- Nat
  #eval let y := 2 + 2; y * y -- 16

  def twice_double (x : Nat) : Nat :=
    let y := x + x; y * y

  #eval twice_double 2 -- 16

  #check let y := 2 + 2; let z := y + y; z * z -- Nat
  #eval let y := 2 + 2; let z := y + y; z * z  -- 64

  def t (x : Nat) : Nat :=
    let y := x + x
    y * y

  #eval t 2 -- 16
end local_definitions


/- Variables and Sections -/

section variables_sections
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose1 := g (f x)
  def doTwice1 := h (h x)
  def doThrice1 := h (h (h x))

  #print compose1
  #print doTwice1
  #print doThrice1
end variables_sections


/- Namespace -/

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7
  def fa : Nat := f a

  #check a 
  #check f
  #check fa
  #check Foo.fa
end Foo

-- #check fa - Error
#check Foo.fa


namespace Foo
  def ffa : Nat := f (f a)
end Foo

#check Foo.ffa

/- Dependent -/

section dependent 
  def cons (α : Type) (a : α) (as : List α) : List α :=
    List.cons a as

  #check cons Nat
  #check cons Bool

  #check @List.cons

  universe u v

  def l (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
    ⟨a, b⟩

  def l1 (x : Nat) : Nat :=
    (l Type (fun a => a) Nat x).2

  #check (l Type (fun a => a) Nat 5).1 -- Type
  #eval l1 5 -- 5
end dependent


/- Implicit arguments -/
section implicit
  universe u
  def Lst (α : Type u) : Type u :=
    List α 
  def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α :=
    List.cons a as
  def Lst.nil {α : Type u} : Lst α :=
    List.nil
  def Lst.append {α : Type u} (as bs : Lst α) : Lst α := 
    List.append as bs
  
  #check Lst.cons 0 Lst.nil


  def ident {α : Type} (x: α) : α := x

  #check ident -- ?m → ?m
  #check ident 1  -- Nat
  #check ident "hello" -- Stirng
  #check @ident -- α → α 

  section 
    variable {α : Type u}
    variable (x : α)
    def identity := x
  end

  #check identity 1 -- Nat
end implicit






