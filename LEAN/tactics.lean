/- Entering Tactic Mode -/

namespace etm
  theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
    apply And.intro
    exact hp
    apply And.intro 
    exact hq 
    exact hp

  #print test

  theorem test1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
    apply And.intro hp; apply And.intro hq hp

  #print test1


  theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
    apply And.intro
    case right => 
      apply And.intro
      exact hq
      exact hp 
    case left => exact hp

  theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
    apply And.intro
    . exact hp
    . apply And.intro 
      . exact hq
      . exact hp
end etm


/- Basic Tactics -/

namespace basic 
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    apply Iff.intro
    . intro h
      apply Or.elim (h.right)
      . intro hq 
        exact Or.inl (And.intro h.left hq)
      . intro hr
        exact Or.inr (And.intro h.left hr)
    . intro h
      apply Or.elim h
      . intro hpq
        exact And.intro hpq.left (Or.inl hpq.right)
      . intro hpr 
        exact And.intro hpr.left (Or.inr hpr.right)

  example (α : Type) : ∀ x : α, x = x := by
    intro a 
    exact rfl

  example : ∀ a b c : Nat, a = b → a = c → b = c := by 
    intro a b c h1 h2
    exact h1.symm.trans h2

  example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
    intro (Exists.intro w h)
    exact Exists.intro w (And.intro h.right h.left)

  example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by 
    intro 
    | (Exists.intro w (Or.inl hp)) => exact (Exists.intro w (Or.inr hp))
    | (Exists.intro w (Or.inr hq)) => exact (Exists.intro w (Or.inl hq))

  example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
    apply Eq.trans h₁
    apply Eq.trans h₂
    assumption 

  example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
    apply Eq.trans  
    assumption 
    apply Eq.trans
    assumption 
    assumption 

  example : ∀ a b c : Nat, a = b → a = c → c = b := by
    intros
    apply Eq.trans
    apply Eq.symm 
    assumption 
    assumption 

  example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic 
    intros 
    apply Eq.trans 
    apply Eq.symm 
    exact a_2 
    exact a_1

  example : ∀ a b c : Nat, a = b → a = c → c = b := by
    intros
    apply Eq.trans
    apply Eq.symm 
    repeat assumption 

  example (x : Nat) : x = x := by
    revert x -- ∀ x, x = x
    intro y -- y = y
    rfl 

  example (x y : Nat) (h : x = y) : y = x := by
    revert h  -- x = y → y = x
    intro h1 -- y = x 
    apply Eq.symm
    assumption 

  
  example (x y : Nat) (h : x = y) : y = x := by
    revert x y -- x = y → y = x
    intros 
    apply Eq.symm
    assumption 

  example : 3 = 3 := by 
    generalize 3 = x  -- x = x
    revert x  -- ∀ x, x = x 
    intro y -- y = y
    rfl 

  example : 2 + 3 = 5 := by 
    generalize h : 3 = x  -- 2 + x = 5
    rw [←h]

end basic 


/- More Tactics -/

namespace more_t 

  example (p q : Prop) : p ∨ q → q ∨ p := by 
    intro h
    cases h with 
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq 

  example (p : Prop) : p ∨ p → p := by 
    intro h 
    cases h
    repeat assumption

  example (p : Prop) : p ∨ p → p := by 
    intro h 
    cases h <;> assumption 

  example (p q : Prop) : p ∨ q → q ∨ p := by
    intro h 
    cases h 
    . apply Or.inr 
      assumption 
    . apply Or.inl 
      assumption 

  example (p q : Prop) : p ∧ q → q ∧ p := by 
    intro h 
    cases h with 
    | intro hp hq => constructor; exact hq; exact hp

  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    apply Iff.intro 
    . intro h
      cases h with 
      | intro hp hqr =>
        cases hqr
        . apply Or.inl; constructor <;> assumption 
        . apply Or.inr; constructor <;> assumption
    . intro h 
      cases h with 
      | inl hpq =>
        cases hpq with
        | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
      | inr hpr =>
        cases hpr with 
        | intro hp hr => constructor; exact hp; apply Or.inr; exact hr 

  example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by 
    intro h 
    cases h with 
    | intro x px => constructor; apply Or.inl; exact px

  def swap_pair : α × β → β × α := by
    intro p 
    cases p 
    constructor <;> assumption

  example (P : Nat → Prop) (h0 : P 0) (h1 : ∀ n, P (Nat.succ n)) (m : Nat) : P m := by 
    cases m with 
    | zero => exact h0
    | succ m' => exact h1 m'

  example (p q : Prop) : p ∧ ¬ p → q := by 
    intro h 
    cases h 
    contradiction 

end more_t


/- Structuring Tactic Proofs -/

namespace struc 

  example (n : Nat) : n + 1 = n.succ := by 
    show n.succ = n.succ 
    rfl

  example : ∃ x, x + 2 = 8 := by 
    let a : Nat := 6
    exists a
    rfl

  /-
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>

  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>

  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }

  -/
end struc 

/- Tactic Combinators -/

namespace tacomb
  
  example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by 
    constructor <;> assumption 

  example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by 
    repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by 
    constructor <;> (try constructor) <;> assumption

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
    constructor
    all_goals (try constructor)
    all_goals assumption 
  
  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
    constructor
    any_goals constructor
    all_goals assumption 

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
    repeat (any_goals constructor)
    all_goals assumption 

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
    repeat (first | constructor | assumption)
end tacomb


/- Rewriting -/

namespace rew 

  example (f : Nat → Nat) (h1 : f 0 = 0) (h2 : k = 0) : f k = 0 := by 
    rw [h2, h1]

  example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
    rw [h hq]; assumption

  example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by 
    rw [Nat.add_zero] at h
    rw [h]

  def Tuple (α : Type) (n : Nat) :=
    { as : List α // as.length = n }

  example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
    rw [h] at t
    assumption 

end rew 


/- Using simplifier -/

namespace usimp 

  example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
    simp; assumption 

  example (xs : List Nat) : List.reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ List.reverse xs := by 
    simp 

  example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
    simp at h; assumption

  attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
  attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

  example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p  (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
    simp at *; constructor <;> assumption

  def f (m n : Nat) : Nat := m + n + m 

  example {m n : Nat} (h : 0 = m) : (f m n) = n := by 
    simp [f, ←h]

  example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
    simp [*]

  example (p q : Prop) (hp : p) : p ∧ q ↔ q := by 
    simp [*]

  example (u w x x' y y' z : Nat)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
    simp at * 
    simp [*]

  
  def mk_symm (xs : List α) := xs ++ xs.reverse

  @[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by 
    simp [mk_symm]

  example (xs ys : List α)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by 
    simp 

  example : if x = 0 then x + y = y else x ≠ 0 := by 
    simp (config := {contextual := true})
    
  example : ∀ (x : Nat) (h : x = 0), y + x = y := by 
    simp (config := {contextual := true})

  example : 0 < x + 1 ∧ x + y + 2 ≥ y + 1 := by
    simp_arith 

end usimp


/- Split -/

namespace split_t 
  def f (x y z : Nat) :=
    match x, y , z with 
    | 5, _, _ => y 
    | _, 5, _ => y 
    | _, _, 5 => y
    | _, _, _ => 1

  example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by 
    intros 
    simp [f]
    split
    . contradiction
    . contradiction
    . contradiction
    . rfl 

  example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by 
    intros 
    simp [f]
    split 
    <;> first | contradiction | rfl 
end split_t


/- Extensible Tactics -/

namespace ext 
  -- Define notation 
  syntax "triv" : tactic 
  
  macro_rules
  | `(tactic| triv) => `(tactic| assumption)

  macro_rules
  | `(tactic| triv) => `(tactic| rfl)

  example (hp : p) : p := by 
    triv 

  example (x : α) : x = x := by 
    triv 
  
  example (x : α) (h : p) : x = x ∧ p := by 
    apply And.intro <;> triv 

  macro_rules
  | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

  example (x : α) (h : p) : x = x ∧ p := by 
    triv 

  

end ext

