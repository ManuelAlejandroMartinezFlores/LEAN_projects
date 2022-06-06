/- One liner -/

example (p q r : Prop) (hp : p)
      : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> try constructor <;> (first | apply Or.inr; apply Or.inl; assumption | repeat apply Or.inr) <;> assumption

/- Propositions and Proofs -/

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by 
  apply Iff.intro <;> intros <;> simp [*]

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;> intro h <;> cases h <;> simp [*]


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by 
  apply Iff.intro <;>
  intros <;> 
  simp [*]

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro 
    | Or.inl (Or.inl _) => simp [*]
    | Or.inl (Or.inr _) => simp [*]
    | Or.inr _ => simp [*]
  . intro
    | Or.inl _ => simp [*]
    | Or.inr (Or.inr _) => simp [*]
    | Or.inr (Or.inl _) => simp [*]


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by 
  apply Iff.intro 
  . intro
    | And.intro _ (Or.inl _) => simp [*]
    | And.intro _ (Or.inr _) => simp [*]
  . intro 
    | Or.inl _ => simp [*]
    | Or.inr _ => simp [*]


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by 
  apply Iff.intro 
  . intro
    | Or.inl _ => simp [*]
    | Or.inr _ => simp [*]
  . intro
    | And.intro hpq hpr => 
      cases hpq with 
      | inl _ => simp [*]
      | inr _ =>
        cases hpr with 
        | inl _ => simp [*]
        | inr _ => simp [*]
       

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by 
  apply Iff.intro 
  . intros; simp [*]
  . intros
    have : p ∧ q := by simp [*]
    simp [*] 


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by 
  apply Iff.intro 
  . intros
    constructor <;> intros <;> simp [*]
  . intro
    intro
    | Or.inl _ => simp [*]
    | Or.inr _ => simp [*]
  
    
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by 
  apply Iff.intro
  . intro h
    have : ¬ p := by 
      intro; show False; apply h; apply Or.inl; assumption
    have : ¬ q := by 
      intro; show False; apply h; apply Or.inr; assumption
    simp [*]
  . intros
    cases (Classical.em (p ∨ q)) with 
    | inl h => cases h <;> simp [*]
    | inr => assumption


example : ¬p ∨ ¬q → ¬(p ∧ q) := by 
  intro h
  have : ¬ (p ∧ q) := by 
    intro
    | And.intro hp hq =>
      cases h with
      | inl hn => exact hn hp
      | inr hn => exact hn hq
  assumption


example : ¬(p ∧ ¬p) := by 
  intro
  | And.intro h hn => exact hn h 
  

example : p ∧ ¬q → ¬(p → q) := by 
  intro
  | And.intro _ hn =>
    intro h
    have : q := by apply h; assumption
    apply hn; assumption

example : ¬p → (p → q) := by 
  intros 
  contradiction


example : (¬p ∨ q) → (p → q) := by 
  intro h _
  cases h with
  | inl => show q; contradiction
  | inr => assumption

example : p ∨ False ↔ p := by 
  apply Iff.intro
  . intro h
    cases h with 
    | inl => assumption
    | inr => apply False.elim; assumption
  . intros; simp [*]


example : p ∧ False ↔ False := by 
  apply Iff.intro 
  . intros 
    simp [*]
  . intros
    apply False.elim 
    assumption

example : (p → q) → (¬q → ¬p) := by 
  intros
  intro 
  have : q := by simp [*]
  show False; contradiction


variable (p q r s : Prop)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by 
  intros 
  cases (Classical.em p)
  . have : r ∨ s := by simp [*]
    cases this with 
    | inl hr => apply Or.inl; exact (fun assumption => hr)
    | inr hs => apply Or.inr; exact (fun assumption => hs)
  . have : p → r := by 
      intro 
      show r; contradiction
    apply Or.inl; assumption

example : ¬(p ∧ q) → ¬p ∨ ¬q := by 
  intro
  cases (Classical.em p) with
  | inl hp => cases (Classical.em q) with 
    | inl hq => apply absurd; exact And.intro hp hq; assumption
    | inr => apply Or.inr; assumption
  | inr => apply Or.inl; assumption


example : ¬(p → q) → p ∧ ¬q := by 
  intro h 
  cases (Classical.em p) with 
  | inl hp => cases (Classical.em q) with 
    | inl hq => apply absurd; exact (fun hp : p => hq); assumption 
    | inr => constructor <;> assumption
  | inr => cases (Classical.em q) with
    | inl => 
      have : p → q := by intro; assumption
      contradiction
    | inr => 
      have : p → q := by intro; contradiction
      contradiction


example : (p → q) → (¬p ∨ q) := by 
  intro 
  cases (Classical.em p) with 
  | inl => simp [*]
  | inr => simp [*]

example : (¬q → ¬p) → (p → q) := by 
  intros
  apply Classical.byContradiction
  intro
  have : ¬ p := by simp [*]
  apply this; assumption


example : p ∨ ¬p := by 
  cases (Classical.em p) with 
  | inl => simp [*]
  | inr => simp [*]

example : (((p → q) → p) → p) := by 
  intro h
  cases (Classical.em (p → q)) with 
  | inl => apply h; assumption
  | inr hn => 
    apply Classical.byContradiction
    intro 
    have : p → q := by simp [*]
    apply hn; exact this




/- Quantifiers and Equality -/


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by 
  intro 
  | Exists.intro _ _ => assumption

example (a : α) : r → (∃ x : α, r) := by 
  intro
  constructor <;> assumption

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by 
  apply Iff.intro
  . intro
    | Exists.intro _ (And.intro _ _) =>
      constructor; constructor <;> assumption; assumption 
  . intro 
    | And.intro (Exists.intro _ _) _ =>
      constructor; constructor <;> assumption


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by 
  apply Iff.intro 
  . intro 
    | Exists.intro _ h => cases h with 
      | inl => apply Or.inl; constructor; assumption
      | inr => apply Or.inr; constructor; assumption
  . intro h 
    cases h with 
    | inl he => 
      let (Exists.intro _ _) := he
      constructor; apply Or.inl; assumption
    | inr he => 
      let (Exists.intro _ _) := he
      constructor; apply Or.inr; assumption

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by  
  apply Iff.intro 
  . intro 
    cases (Classical.em (∃ x, ¬ p x)) with 
    | inl h => 
      let (Exists.intro x _) := h
      have : p x := by simp [*]
      contradiction
    | inr => assumption
  . intro 
    intro x 
    cases (Classical.em (p x)) with 
    | inl => assumption
    | inr =>
      have : ∃ x, ¬ p x := by constructor <;> assumption
      contradiction

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by 
  apply Iff.intro 
  . intro 
    | Exists.intro x _ => 
      intro
      have : ¬ p x := by simp [*]
      contradiction
  . intro 
    apply Classical.byContradiction
    intro 
    have : ∀ x, ¬ p x := by
      intro
      intro 
      have : ∃ x, p x := by constructor <;> assumption 
      contradiction
    contradiction

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by 
  apply Iff.intro 
  . repeat intro
    have : ∃ x, p x := by constructor <;> assumption
    contradiction
  . intro 
    cases (Classical.em (∃ x, p x)) with
    | inl he =>
      let (Exists.intro x _) := he 
      have : ¬ p x := by simp [*]
      contradiction
    | inr => assumption


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by 
  apply Iff.intro 
  . intro 
    apply Classical.byContradiction
    intro 
    have : ∀ x, p x := by 
      intro
      apply Classical.byContradiction
      intro 
      have : ∃ x, ¬ p x := by constructor <;> assumption
      contradiction
    contradiction
  . intro 
    | Exists.intro x _ =>
      cases (Classical.em (∀ x, p x)) with 
      | inl =>
        have : p x := by simp [*]
        contradiction
      | inr => assumption

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by 
  apply Iff.intro 
  . intro h
    intro
    | Exists.intro x _ => 
      have : p x → r := h x 
      simp [*]
  . intros
    have : ∃ x, p x := by constructor <;> assumption
    simp [*]

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by 
  apply Iff.intro 
  . intro
    | Exists.intro _ _ =>
      intro 
      simp [*]
  . intro 
    cases (Classical.em (∀ x, p x)) with 
    | inl => 
      have : p a := by simp [*]
      exists a; simp [*]
    | inr => 
      apply Classical.byContradiction
      intro 
      have : ∀ x, p x := by 
        intro x
        apply Classical.byContradiction
        intro
        have : ∃ x, p x → r := by exists x; intro; contradiction
        contradiction
      contradiction

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by 
  apply Iff.intro 
  . intro
    | (Exists.intro x _), _ => 
      have : p x := by simp [*]
      constructor <;> assumption
  . intro 
    cases (Classical.em r) with 
    | inl => 
      have : ∃ x, p x := by simp [*]
      let (Exists.intro x _) := this
      exists x; simp [*]
    | inr => 
      have : r → p a := by intro; contradiction
      constructor <;> assumption


variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=  by 
  apply Iff.intro 
  . intro
    constructor <;> intro <;> simp [*]
  . intros
    constructor <;> simp [*]

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by 
  intros
  simp [*]

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by 
  intro
  | Or.inl _, _ => apply Or.inl; simp [*]
  | Or.inr _, _ => apply Or.inr; simp [*]



variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by 
  intro
  apply Iff.intro 
  . intro h; apply h; assumption
  . intro; intro; assumption

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by 
  apply Iff.intro 
  . intro h 
    cases (Classical.em r) with 
    | inl => simp [*]
    | inr => 
      have : ∀ x, p x := by 
        intro x; 
        have : p x ∨ r := h x
        cases this with 
          | inl => assumption
          | inr => contradiction
      simp [*] 
  . intro
    | Or.inl _, x => apply Or.inl; simp [*] 
    | Or.inr _, x => apply Or.inr; assumption


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by 
  apply Iff.intro 
  . intros
    simp [*]
  . intros 
    simp [*]


variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by 
  cases (Classical.em (shaves barber barber)) with 
  | inl hb => exact ((h barber).mp hb) hb
  | inr hnb => exact hnb ((h barber).mpr hnb)

