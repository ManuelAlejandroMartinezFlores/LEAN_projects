variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun h : p ∧ q =>
      have hp : p := h.left
      have hq : q := h.right
      show q ∧ p from ⟨hq, hp⟩)
    (fun h : q ∧ p =>
      have hq : q := h.left
      have hp : p := h.right
      show p ∧ q from And.intro hp hq)


example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
        (fun hp : p => show q ∨ p from Or.inr hp)
        (fun hq : q => show q ∨ p from Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h
        (fun hq : q => show p ∨ q from Or.inr hq)
        (fun hp : p => show p ∨ q from Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro 
    (fun h : (p ∧ q) ∧ r =>
      have hpq : p ∧ q := h.left
      have hp : p := hpq.left
      have hq : q := hpq.right
      have hr : r := h.right
      show p ∧ (q ∧ r) from And.intro hp (And.intro hq hr))
    (fun h : p ∧ (q ∧ r) =>
      have hp : p := h.left
      have hqr : q ∧ r := h.right
      have hq : q := hqr.left
      have hr : r := hqr.right
      show (p ∧ q) ∧ r from And.intro (And.intro hp hq) hr)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      Or.elim h
        (fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p => show p ∨ (q ∨ r) from Or.inl hp)
            (fun hq : q => show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))  
        (fun hr : r => show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      Or.elim h
        (fun hp : p => show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q => show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
            (fun hr : r => show (p ∨ q) ∨ r from Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      have hqr : q ∨ r := h.right
      Or.elim hqr
        (fun hq : q => show (p ∧ q) ∨ (p ∧ r) from Or.inl (And.intro hp hq))
        (fun hr : r => show (p ∧ q) ∨ (p ∧ r) from Or.inr (And.intro hp hr)))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from And.intro hp (Or.inl hq))
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from And.intro hp (Or.inr hr)))



example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro 
    (fun h : p ∨ (q ∧ r) =>
      Or.elim h
        (fun hp : p =>
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.inl hp) (Or.inl hp))
        (fun hqr : q ∧ r =>
          have hq : q := hqr.left
          have hr : r := hqr.right
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.inr hq) (Or.inr hr)))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := h.left
      have hpr : p ∨ r := h.right
      Or.elim hpq 
        (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
          Or.elim hpr
            (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp)
            (fun hr : r => show p ∨ (q ∧ r) from Or.inr (And.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro 
    (fun h : p → (q → r) =>
      fun hpq : p ∧ q =>
        have hp : p := hpq.left
        have hq : q := hpq.right
        show r from h hp hq)
    (fun h : p ∧ q → r =>
      fun hp : p =>
        fun hq : q =>
          show r from h (And.intro hp hq))


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro
    (fun h : (p ∨ q) → r =>
      show (p → r) ∧ (q → r) from And.intro
        (fun hp : p =>
          show r from h (Or.inl hp))
        (fun hq : q =>
          show r from h (Or.inr hq)))
    (fun h : (p → r) ∧ (q → r) =>
      have hpr : p → r := h.left
      have hqr : q → r := h.right
      fun hpq : p ∨ q =>
        Or.elim hpq
          (fun hp : p => show r from hpr hp)
          (fun hq : q => show r from hqr hq))


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro 
    (fun h : ¬(p ∨ q) =>
      Or.elim (Classical.em p)
        (fun hp : p => absurd (Or.inl hp) h)
        (fun hnp : ¬p =>
          Or.elim (Classical.em q)
            (fun hq : q => absurd (Or.inr hq) h)
            (fun hnq : ¬q => show ¬p ∧ ¬q from And.intro hnp hnq)))
    (fun h : ¬p ∧ ¬q =>
      Or.elim (Classical.em (p ∨ q))
        (fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p => absurd hp h.left)
            (fun hq : q => absurd hq h.right))
        (fun hnpq : ¬(p ∨ q) => hnpq))


example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  fun h : ¬p ∨ ¬q =>
    Or.elim h
      (fun hnp : ¬p =>
        Or.elim (Classical.em (p ∧ q))
          (fun hpq : p ∧ q =>
            absurd hpq.left hnp)
          (fun hnpq : ¬(p ∧ q) => hnpq))
      (fun hnq : ¬q =>
        Or.elim (Classical.em (p ∧ q))
          (fun hpq : p ∧ q =>
            absurd hpq.right hnq)
          (fun hnpq : ¬(p ∧ q) => hnpq))


example : ¬(p ∧ ¬p) := 
  Or.elim (Classical.em (p ∧ ¬p))
    (fun h : p ∧ ¬p => absurd h.left h.right)
    (fun hn : ¬(p ∧ ¬p) => hn)


example : p ∧ ¬q → ¬(p → q) := 
  fun h : p ∧ ¬q =>
    Or.elim (Classical.em (p → q))
      (fun hpq : p → q => 
        have h₁ : q := hpq h.left
        have h₂ : ¬q := h.right
        absurd h₁ h₂)
      (fun hn : ¬(p → q) => hn)


example : ¬p → (p → q) := 
  fun h : ¬p =>
    fun hp : p => show q from absurd hp h


example : (¬p ∨ q) → (p → q) := 
  fun h : ¬p ∨ q =>
    Or.elim h
      (fun hnp : ¬p =>
        fun hp : p => absurd hp hnp)
      (fun hq : q =>
        fun hp : p => hq)


example : p ∨ False ↔ p := 
  Iff.intro 
    (fun h : p ∨ False =>
      Or.elim h
        (fun hp : p => hp)
        (fun hf : False => False.elim hf))
    (fun h : p => show p ∨ False from Or.inl h)


example : p ∧ False ↔ False := 
  Iff.intro
    (fun h : p ∧ False =>
      False.elim h.right)
    (fun h : False => show p ∧ False from False.elim h)


example : (p → q) → (¬q → ¬p) := 
  fun h : p → q =>
    fun hnq : ¬q =>
      Or.elim (Classical.em p)
        (fun hp : p => absurd (h hp) hnq)
        (fun hnp : ¬p => hnp)



variable (p q r s : Prop)


example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
  fun h : p → r ∨ s =>
    Classical.byCases
      (fun hp : p => 
        Or.elim (h hp)
          (fun hr : r => show (p → r) ∨ (p → s) from Or.inl (fun hp => hr))
          (fun hs : s => show (p → r) ∨ (p → s) from Or.inr (fun hp => hs)))
      (fun hnp : ¬p => 
        have hpr : p → r := (fun hp => absurd hp hnp)
        show (p → r) ∨ (p → s) from Or.inl hpr)



example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  fun h : ¬(p ∧ q) =>
    Or.elim (Classical.em p)
      (fun hp : p => 
        Or.elim (Classical.em q)
          (fun hq : q => absurd (And.intro hp hq) h)
          (fun hnq : ¬q => show ¬p ∨ ¬q from Or.inr hnq))
      (fun hnp : ¬p => show ¬p ∨ ¬q from Or.inl hnp)


example : ¬(p → q) → p ∧ ¬q := 
  fun h : ¬(p → q) =>
    Classical.byCases
      (fun hp : p => 
        Classical.byCases
          (fun hq : q => absurd (fun hp => hq) h)
          (fun hnq : ¬q => And.intro hp hnq))
      (fun hnp : ¬p => 
        Classical.byCases
          (fun hq : q =>
            have hpq : p → q := (fun hp => hq)
            absurd hpq h)
          (fun hnq : ¬q =>
            have hpq : p → q := 
              (fun hp : p => absurd hp hnp)
            absurd hpq h))

example : (p → q) → (¬p ∨ q) := 
  fun h : p → q =>
    Or.elim (Classical.em p)
      (fun hp : p => show ¬p ∨ q from Or.inr (h hp))
      (fun hnp : ¬p => show ¬p ∨ q from Or.inl hnp)


example : (¬q → ¬p) → (p → q) := 
  fun h : ¬q → ¬p =>
    fun hp : p =>
      Or.elim (Classical.em q)
        (fun hq : q => hq)
        (fun hnq : ¬q => absurd hp (h hnq))


example : p ∨ ¬p := 
  Classical.byCases
    (fun hp : p => show p ∨ ¬p from Or.inl hp)
    (fun hnp : ¬p => show p ∨ ¬p from Or.inr hnp)


example : (((p → q) → p) → p) := 
  fun h : (p → q) → p =>
    Classical.byCases
      (fun hpq : p → q => h hpq)
      (fun hnpq : ¬ (p → q) =>
        Classical.byContradiction
          (fun hnp : ¬ p => 
           have hpq : p → q := (fun hp : p => absurd hp hnp)
           show False from hnpq hpq))
    
    
