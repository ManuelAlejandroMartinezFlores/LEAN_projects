/- constants -/

def m : Nat := 1  -- natural 
def n : Nat := 0
def b1 : Bool := true -- boolean
def b2 : Bool := false


/- check types -/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2 -- && is and
#check b1 || b2 -- || is or
#check true


/- Evaluate -/

#eval 4 * 5
#eval m + 2
#eval b1 && b2


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


/- function abstraction -/
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




