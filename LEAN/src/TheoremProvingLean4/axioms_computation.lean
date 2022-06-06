/- Propositional Extensionality -/

namespace pe 

  axiom propext {a b : Prop} : (a ↔ b) → a = b 

  theorem th1 (a b c d e : Prop) (h : a ↔ b)
      : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ Iff.refl _

  theorem th2 (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h1 : p a) : p b :=
    propext h ▸ h1 

end pe


/- Function Extensionality -/

namespace fe 

  universe u v
  #check (@funext :
            {α : Type u}
          → {β : α → Type u}
          → {f g : (x : α) → β x}
          → (∀ (x : α), f x = g x)
          → f = g)

  #print funext


  def Set (α : Type u) := α → Prop 

  namespace Set 

    def mem (x : α) (s : Set α) := s x 

    infix:50 (priority := high) "∈" => mem 

    theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b)
        : a = b :=
      funext (fun x => propext (h x))

    def empty : Set α := fun x => False 

    notation (priority := high) "∅" => empty 

    def inter (a b : Set α) : Set α := 
      fun x => a x ∧ b x 

    infix:70 " ∩ " => inter 

    theorem inter_self (a : Set α) : a ∩ a = a :=
      setext fun x => Iff.intro 
        (fun (And.intro h _) => h) -- a x → a x
        (fun h => And.intro h h) -- a x → a x ∧ a x

    theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ := 
      setext fun x => Iff.intro 
        (fun (And.intro _ h) => h)
        (fun h => False.elim h)

    theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ := 
      setext fun x => Iff.intro
        (fun (And.intro h _) => h)
        (fun h => False.elim h)

    theorem inter_comm (a b : Set α) : a ∩ b = b ∩ a := 
      setext fun x => Iff.intro 
        (fun (And.intro ha hb) => And.intro hb ha)
        (fun (And.intro hb ha) => And.intro ha hb)

  end Set


end fe


/- Quotients -/

namespace quo 

  universe u v

  axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u 

  axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r 

  axiom Quot.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q 

  axiom Quot.lift : {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
      → (∀ a b, r a b → f a = f b) → Quot r → β 

  def mod7rel (a b : Nat) : Prop :=
    a % 7 = b % 7 

  #check (Quot mod7rel : Type) 

  #check (Quot.mk mod7rel 4 : Quot mod7rel) -- equiv class

  def f (x : Nat) : Bool := 
    x % 7 = 0

  theorem f_respects (a b : Nat) (h : mod7rel a b) : f a = f b := by 
    simp [mod7rel, f]
    rw [h]

  axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
      r a b → Quot.mk r a = Quot.mk r b 

  
  class Setoid (α : Sort u) where
    r : α → α → Prop 
    iseq : Equivalence r 

  instance {α : Sort u} [Setoid α] : HasEquiv α := 
    HasEquiv.mk Setoid.r 

  namespace Setoid

    variable {α : Sort u} [Setoid α]

    theorem refl (a : α) : a ≈ a := 
      iseq.refl a 

    theorem symm (a b : α) (h : a ≈ b) : b ≈ a :=
      iseq.symm h 

    theorem trans (a b c : α) (h1 : a ≈ b) (h2 : b ≈ c) : a ≈ c :=
      iseq.trans h1 h2 

  end Setoid

  def Quotient {α : Sort u} (s : Setoid α) :=
    @Quot α Setoid.r 

end quo


namespace eq 

  private def eqv (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

  infix:50 "~" => eqv 

  private theorem eqv.refl (p : α × α) : p ~ p := 
    Or.inl (And.intro rfl rfl)

  private theorem eqv.symm : ∀ {p q : α × α}, p ~ q →  q ~ p := by
    intro p q h 
    match h with 
    | Or.inl (And.intro h1 h2) => exact Or.inl (And.intro h1.symm h2.symm)
    | Or.inr (And.intro h1 h2) => exact Or.inr (And.intro h2.symm h1.symm)

  private theorem eqv.trans : ∀ {p q r : α × α}, p ~ q → q ~ r → p ~ r := by 
    intro p q r hp hq
    match hp with 
    | Or.inl (And.intro h1 h2) => match hq with
      | Or.inl (And.intro h3 h4) => apply Or.inl; constructor; exact h1.trans h3; exact h2.trans h4
      | Or.inr (And.intro h3 h4) => apply Or.inr; constructor; exact h1.trans h3; exact h2.trans h4
    | Or.inr (And.intro h1 h2) => match hq with
      | Or.inl (And.intro h3 h4) => apply Or.inr; constructor; exact h1.trans h4; exact h2.trans h3
      | Or.inr (And.intro h3 h4) => apply Or.inl; constructor; exact h1.trans h4; exact h2.trans h3

  private theorem is_equivalence : Equivalence (@eqv α) :=
    {refl := eqv.refl, symm := eqv.symm, trans := eqv.trans}

  instance uprodSetoid (α : Type u) : Setoid (α × α) where 
    r := eqv 
    iseqv := is_equivalence

  def UProd (α : Type u) : Type u := 
    Quotient (uprodSetoid α)

    namespace UProd

      def mk {α : Type} (a₁ a₂ : α) : UProd α :=
        Quotient.mk' (a₁, a₂)

      notation "{" a ", " b "}" => mk a b 

      theorem mk_eq_mk (a b : α) : {a, b} = {b, a} := 
        Quot.sound (Or.inr (And.intro rfl rfl))

      private def mem_fn (a : α) : α × α → Prop 
        | (b, c) => a = b ∨ a = c

      private theorem mem_swap {a : α} :
          ∀ {p : α × α}, mem_fn a p = mem_fn a (p.2, p.1) := by
        intro
        | (b, c) => 
          apply propext 
          apply Iff.intro 
          . intro 
            | Or.inl h => exact Or.inr h 
            | Or.inr h => exact Or.inl h 
          . intro
            | Or.inl h => exact Or.inr h
            | Or.inr h => exact Or.inl h 

      private theorem mem_respects 
          : {p q : α × α} → (a : α) → p ~ q → mem_fn a p = mem_fn a q 
        | (b, c), (d, e), a, (Or.inl (And.intro bd ce)) => by simp_all
        | (b, c), (d, e), a, (Or.inr (And.intro bd ce)) => by simp_all; apply mem_swap

    end UProd

end eq


/- Axiom of Choice -/

namespace ch 

  universe u

  class inductive Nonempty (α : Sort u) : Prop where 
    | intro : (val : α) → Nonempty α

  example (α : Type u) : Nonempty α ↔ ∃ x : α, True := 
    Iff.intro (fun (Nonempty.intro a) => Exists.intro a trivial) (fun (Exists.intro a _) => Nonempty.intro a)

  axiom choice {α : Sort u} : Nonempty α → α 

  noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) 
      (h : ∃ x, p x) : {x // p x} := 
    choice <| let (Exists.intro x px) := h; ⟨⟨x, px⟩⟩ 

end ch


/- Law of the Excluded Middle -/

namespace lem 

  open Classical 

  theorem em (p : Prop) : p ∨ ¬ p := 
    let U (x : Prop) := x = True ∨ p 
    let V (x : Prop) := x = False ∨ p

    have exU : ∃ x, U x := Exists.intro True (Or.inl rfl)
    have exV : ∃ x, V x := Exists.intro False (Or.inl rfl)

    let u : Prop := choose exU
    let v : Prop := choose exV

    have u_def : U u := choose_spec exU
    have v_def : V v := choose_spec exV

    have not_uv_or_p : u ≠ v ∨ p := 
      match u_def, v_def with 
      | Or.inr h, _ => Or.inr h 
      | _, Or.inr h => Or.inr h 
      | Or.inl hu, Or.inl hv =>
        have hn : u ≠ v := by simp [hu, hv]
        Or.inl hn

    have p_implies_uv : p → u = v := 
      fun hp =>  
      have hpred : U = V := 
        funext fun x => 
          have hl : (x = True ∨ p) → (x = False ∨ p) :=
            fun _ => Or.inr hp 
          have hr : (x = False ∨ p) → (x = True ∨ p) := 
            fun _ => Or.inr hp 
          show (x = True ∨ p) = (x = False ∨ p) from
            propext (Iff.intro hl hr)
      have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by 
        rw [hpred]; intros; rfl 
      show u = v from h₀ _ _ 

    match not_uv_or_p with 
    | Or.inl hne => Or.inr (mt p_implies_uv hne)
    | Or.inr hp => Or.inl hp 

  

end lem