/- Propositions as Types -/
namespace prop_as_types
  def Implies (p q : Prop) : Prop := p → q
  #check And -- Prop → Prop → Prop
  #check Or  
  #check Implies  
  #check Not -- Prop → Prop

  variable (p q r : Prop)
  #check And p q -- Prop
  #check Or (And p r) q -- Prop
  #check implies p q -- Prop

  structure Proof (p : Prop) : Type where
    proof : p
  #check Proof -- Prop → Type

  axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))
  #check and_comm p q

  axiom modus_ponens : (p q : Prop) →  Proof (Implies p q) → Proof p → Proof q
  axiom implies_intro (p q : Prop) : (Proof p → Proof q) → Proof (Implies p q)
end prop_as_types


/- Working with Propositions as Types -/

namespace work_wpt
  variable {p : Prop} {q : Prop}
  theorem t1 : p → q → p := 
    fun hp : p => 
    fun hq : q => 
    show p from hp
  #print t1

  theorem t1_ (hp : p) (hq : q) : p := show p from hp
  #print t1_

  axiom hp : p
  theorem t2 : p → q := t1 hp
  
  axiom unsound : False
  theorem ex : 1 = 0 :=
    False.elim unsound
  #print ex

  theorem t1_1 (p q : Prop) (hp : p) (hq : q) : p := hp
  variable (p q r s : Prop)
  #check t1_1 p q

  variable (h : r → s)
  #check t1_1 (r → s) (s → r) h

  theorem t2_1 (h₁ : q → r) (h₂ : p → q) : p → r :=
    fun h₃ : p => 
    show r from h₁ (h₂ h₃)
  #print t2_1
  #check t2_1 p q r -- (q → r) → (p → q) → p → r
end work_wpt

/- Propositional Logic -/

namespace prop_log
  variable (p q : Prop)
  #check p → q → p ∧ q
  #check ¬p → p ↔ False
  #check p ∨ q → q ∨ p
end prop_log

namespace conj
  variable (p q : Prop)
  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
  example (h : p ∧ q) : q := And.right h
  example (h : p ∧ q) : p := And.left h

  example (h: p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)

  variable (hp: p) (hq : q)
  #check (⟨hp, hq⟩ : p ∧ q)

  variable (xs : List Nat)
  #check List.length xs
  #check xs.length

  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩

  example (h : p ∧ q) : p ∧ q ∧ p :=
    ⟨h.left, h.right, h.left⟩ 
end conj

namespace disj
  variable (p q r : Prop)
  example (hp : p) : p ∨ q := Or.intro_left q hp
  example (hq : q) : p ∨ q := Or.intro_right p hq

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)
  
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
end disj

/- Negation and Falsity -/

namespace neg_f
  variable (p q r : Prop)

  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)

  example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
  example (hp : p) (hnp : ¬p) : q := absurd hp hnp

  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp
end neg_f


/- Logical Equivalence -/

namespace logeq
  variable (p q : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro 
      (fun h : p ∧ q =>
        show q ∧ p from And.intro h.right h.left)
      (fun h : q ∧ p =>
        show p ∧ q from And.intro h.right h.left)
  
  #check and_swap p q
  
  variable (h : p ∧ q)
  example : q ∧ p := Iff.mp (and_swap p q) h
end logeq

/- Auxiliary subgoals -/

namespace aux_sub
  variable (p q r : Prop)

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    suffices hq : q from And.intro hq hp
    show q from h.right
end aux_sub


/- Classical Logic -/

namespace class_log
  open Classical

  variable (p q r : Prop)

  #check em p

  theorem dne {p : Prop} (h : ¬¬p) : p :=
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => absurd hnp h)

  theorem my_em : p ∨ ¬p :=
    byCases
      (fun h : p =>
        Or.intro_left (¬p) h)
      (fun h : ¬p =>
        Or.intro_right p h)

    
  example (h : ¬¬p) : p :=
    byContradiction
      (fun h1 : ¬p =>
        show False from h h1)


  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    Or.elim (em p)
      (fun hp : p =>
        Or.inr 
          (show ¬q from
            fun hq : q =>
              h ⟨hp, hq⟩))
      (fun hnp : ¬p =>
        Or.inl hnp)
end class_log

-- Examples
namespace ex
  open Classical
  variable (p q r : Prop)

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
      (fun h : p ∧ (q ∨ r) =>
        have hp : p := h.left
        Or.elim (h.right)
          (fun hq : q =>
            show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
          (fun hr : r =>
            show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
      
      (fun h : (p ∧ q) ∨ (p ∧ r) =>
        Or.elim h
          (fun hpq : p ∧ q =>
            have hp : p := hpq.left
            have hq : q := hpq.right
            show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
          (fun hpr : p ∧ r =>
            have hp : p := hpr.left
            have hr : r := hpr.right
            show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

  -- classical example
  example : ¬(p ∧ ¬q) → (p → q) :=
    fun h : ¬(p ∧ ¬q) =>
      fun hp : p =>
        show q from
          Or.elim (em q)
            (fun hq : q => hq)
            (fun hnq : ¬q =>
              absurd ⟨hp, hnq⟩ h)

end ex

