/- Type classes -/


namespace tp 

  structure Add1 (α : Type u) where
    add : α → α → α 

  def double (s : Add1 α) (x : α) :=
    s.add x x

  #eval double {add := Nat.add} 10 -- 20

  class Add (α : Type u) where
    add : α → α → α 

  instance : Add Nat where
    add := Nat.add

  instance [Add α] : Add (Array α) where 
    add x y := Array.zipWith x y (Add.add . .)

  #eval Add.add #[1, 2] #[3, 4] -- #[4, 6]

  namespace Ex

    class Inhabited (α : Type u) where 
      default : α 

    instance : Inhabited Bool where 
      default := true 

    instance : Inhabited Nat where 
      default := 0

    export Inhabited (default)

    #eval (default : Nat)  -- 0
    #eval (default : Bool) -- true

  end Ex 
end tp 


/- Chaining Instances -/

namespace ci 

  instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where 
    default := (default, default)

  #eval (default : Nat × Bool) -- (0, false)

  instance [Inhabited β] : Inhabited (α → β) where 
    default := fun _ => default 

  instance [Inhabited α] : Inhabited (List α) where 
    default := [default]

  #eval (default : List Nat) -- [0]

  instance [Inhabited α] : Inhabited (Sum α β) where 
    default := Sum.inl default 

  #print inferInstance 

end ci


/- ToString -/

namespace ts  

  structure Person where
    name : String 
    age : Nat 

  instance : ToString Person where 
    toString p := p.name ++ "@" ++ toString p.age 

  #eval toString ({name := "Leo", age := 25 : Person}, 10) -- "(Leo@25, 10)"
end ts 


/- Numerals -/

namespace num 

  structure Rational where
    num : Int 
    den : Nat 
    inv : den ≠ 0 

  instance : OfNat Rational n where 
    ofNat := {num := n, den := 1, inv := by decide}

  instance : ToString Rational where 
    toString r := s!"{r.num}/{r.den}"

  #eval (2 : Rational) -- 2/1

  class Monoid (α : Type u) where 
    unit : α 
    op : α → α → α 

  instance [s : Monoid α] : OfNat α (nat_lit 1) where 
    ofNat := s.unit

  def getUnit [Monoid α] : α :=
    1 

end num 


/- Output Parameters -/

namespace op  

  class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where 
    hMul : α → β → γ 

  export HMul (hMul)

  instance : HMul Nat Nat Nat where 
    hMul := Nat.mul

  instance [HMul α β γ]: HMul α (Array β) (Array γ) where 
    hMul a bs := bs.map (fun b => hMul a b)

  #eval hMul 3 #[1, 2] -- #[3, 6]

  #eval hMul 3 #[#[1, 2], #[3]] -- #[#[3, 6], #[9]]

end op 


/- Defalut instances -/

namespace di 

  class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where 
    hMul : α → β → γ 

  export HMul (hMul)

  @[defaultInstance]
  instance : HMul Int Int Int where 
    hMul := Int.mul 

  #check (fun y => [1, 2].map (fun x => hMul y x)) -- Int → List Int 

  class Mul (α : Type u) where 
    mul : α → α → α 

  @[defaultInstance 10]
  instance [Mul α] : HMul α α α  where 
    hMul := Mul.mul

end di


/- Local Instances -/

namespace li  

  structure Point where 
    x : Nat 
    y : Nat 

  section 
    local instance addPoint : Add Point where 
      add p q := {x := p.x + q.x, y:= p.y + q.y}

    attribute [-instance] addPoint 
  end 
end li 


/- Scoped Instances -/

namespace si  

  structure Point where 
    x : Nat 
    y : Nat 

  namespace Point 
    scoped instance addPoint : Add Point where 
      add p q := {x := p.x + q.x, y:= p.y + q.y}
  end Point 

end si


/- Decidable Propositions -/

namespace dp 

  class inductive Decidable (p : Prop) where
  | isFalse (h : ¬ p) : Decidable p
  | isTrue (h : p) : Decidable p 

  def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
    match h with 
    | Decidable.isTrue _  => t
    | Decidable.isFalse _ => e 

  def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : ¬ c → α) : α :=
    match h with 
    | Decidable.isTrue c => t c
    | Decidable.isFalse nc => e nc 

  example : ¬ (True ∧ False) := by decide 

end dp 

/- Managing Type Class Inference -/

namespace mtci 

  def foo : Inhabited (Nat → Nat) := inferInstance

  def Set (α : Type u) := α → Prop 

  example : Inhabited (Set α) := 
    inferInstanceAs (Inhabited (α → Prop))

end mtci


/- Coercions using Type Classes-/

namespace coer 

  instance : Coe Bool Prop where 
    coe b := b = true 

  #eval if true then 5 else 3 -- 5

  def Set (α : Type u) := α → Prop 
  def Set.empty {α : Type u} : Set α := fun _ => False 
  def Set.mem (a : α) (s : Set α) : Prop := s a 
  def Set.singleton (a : α) : Set α := fun x => x = a 
  def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x 
  notation "{" a "}" => Set.singleton a 
  infix:55 " ∪ " => Set.union


  def List.toSet : List α → Set α
    | []    => Set.empty
    | a::as => {a} ∪ toSet as 

  instance : Coe (List α) (Set α) where 
    coe as := List.toSet as 

  /-
  {1} ∪ List.toSet [1, 2] : Set Nat
  -/
  #check {1} ∪ ↑[1, 2] 


  instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where 
    coe := decide p 

  
  structure Semigroup where 
    carrier : Type u
    mul : carrier → carrier → carrier 
    mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

  instance (S : Semigroup) : Mul S.carrier where 
    mul := S.mul 

  instance : CoeSort Semigroup (Type u) where 
    coe s := s.carrier 

  example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) := 
    S.mul_assoc a b c 


  structure Morphism (S1 S2 : Semigroup) where 
    mor : S1 → S2 
    resp_mul : ∀ a b : S1, mor (a * b) = mor a * mor b 
  
  #check @Morphism.mor

  instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where 
    coe m := m.mor 

  theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
      : f (a * b) = f a * f b := f.resp_mul a b 

  example {S1 S2 : Semigroup} (f : Morphism S1 S2) (a : S1)
      : f (a * a * a) = f a * f a * f a := by simp only [resp_mul]

      


end coer