/- Universal quantifier -/

namespace uni_q
  example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → (∀ y : α, q y) :=
    fun h : ∀ x : α, p x ∧ q x =>
      fun y : α =>
        show q y from (h y).right

  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ x y z, r x y → r y z → r x z)
  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  #check trans_r a -- (∀ y z : α), r a y → r y z → r a z
  #check trans_r a b -- (∀ z : α), r a b → r b z → r a z
  #check trans_r a b c -- r a b → r b c → r a c
  #check trans_r a b c hab -- r b c → r a c
  #check trans_r a b c hab hbc -- r a c

  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)
  #check trans_r hab hbc -- r a c


  /- Equivalence relation -/
  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)
  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd
end uni_q


/- Equality -/

namespace equality 
  universe u
  #check @Eq.refl.{u} -- a = a
  #check @Eq.symm.{u} -- a = b → b = a
  #check @Eq.trans.{u} -- a = b → b = c → a = c

  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)
  example : a = d :=
    Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
  example : a = d := (hab.trans hcb.symm).trans hcd


  variable (α β : Type) (a b c d : α)

  example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl (f a)
  example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
  example : (a, b).1 = a := Eq.refl a
  example : 2 + 3 = 5 := rfl


  -- Substitution
  example (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
    Eq.subst h1 h2

  example (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
    h1 ▸ h2  -- "▸" "t"
  
  variable (f g : α → ℕ) 
  variable (h1 : f = g) (h2 : a = b)
  example : f a = f b := congrArg f h2
  example : f a = g a := congrFun h1 a
  example : f a = g b := congr h1 h2

  variable (a b c d : Nat) 
  example : a + 0 = a := a.add_zero
  example : 0 + a = a := a.zero_add
  example : a * 1 = a := a.mul_one
  example : 1 * a = a := a.one_mul
  example : a + b = b + a := a.add_comm b
  example : a + b + c = a + (b + c) := a.add_assoc b c
  example : a * b = b * a := a.mul_comm b 
  example : a * b * c = a * (b * c) := a.mul_assoc b c
  example : a * (b + c) = a * b + a * c := a.mul_add b c
  example : (a + b) * c = a * c + b * c := a.add_mul b c

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
      Nat.mul_add (x + y) x y
    have h2 : (x + y) * (x + y) = (x * x + y * x) + (x * y + y * y) :=
      (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
    h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

end equality


/- Calculation Proofs -/

namespace calc_p
  variable (a b c d e : Nat)
  variable (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d)
  theorem T : a = e :=
    calc
      a = b := h1
      _ = c + 1 := h2
      _ = d + 1 := congrArg Nat.succ h3
      _ = 1 + d := Nat.add_comm d 1
      _ = e := h4.symm

  theorem T1 : a = e :=
    calc 
      a = b := by rw [h1]
      _ = c + 1 := by rw [h2]
      _ = d + 1 := by rw [h3]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e := by rw [h4]

  theorem T2 : a = e :=
    calc
      a = d + 1 := by rw [h1, h2, h3]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e := by rw [h4]

  theorem T3 : a = e :=
    by rw [h1, h2, h3, Nat.add_comm, h4]

  example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
    calc
      a = b := h1
      _ < b + 1 := Nat.lt_succ_self b
      _ ≤ c + 1 := Nat.succ_le_succ h2
      _ < d := h3

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc
      (x + y) * (x + y) = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
 
end calc_p


/- Existencial Quantifier -/

namespace exist
  #check @Exists.intro
  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    Exists.intro 1 h

  example (x : Nat) (h : x > 0) : ∃ y : Nat, y < x :=
    Exists.intro 0 h

  example (x y z : Nat) (h1 : x < y) (h2 : y < z) : ∃ w, x < w ∧ w < z :=
    Exists.intro y (And.intro h1 h2)

  variable (g : Nat → Nat → Nat)


  variable (hg : g 0 0 = 0)

  theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.explicit true  -- display implicit arguments
  #print gex1
  #print gex2
  #print gex3
  #print gex4


  variable (α : Type) (p q : α → Prop)
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    Exists.elim h
      (fun w =>
        fun hw : p w ∧ q w =>
          show ∃ w, q w ∧ p w from Exists.intro w (And.intro hw.right hw.left))

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | Exists.intro w hw => Exists.intro w (And.intro hw.right hw.left)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | Exists.intro w (And.intro hpw hqw) => Exists.intro w (And.intro hqw hpw)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    let (Exists.intro w (And.intro hpw hqw)) := h
    Exists.intro w (And.intro hqw hpw)


  def is_even (a : Nat) := ∃ b : Nat, a = 2 * b

  theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    match h1, h2 with
    | Exists.intro w1 hw1, Exists.intro w2 hw2 =>
        Exists.intro (w1 + w2)
          (calc
            a + b = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
            _ = 2 * (w1 + w2) := by simp [Nat.mul_add])

  
  example (h : ¬ ∀ x, ¬p x) : ∃ x, p x :=
    Classical.byContradiction
      (fun h1 : ¬ ∃ x, p x =>
        have h2 : ∀ x, ¬p x :=
          fun x => 
            fun h3 : p x =>
              have h4 : ∃ x, p x := Exists.intro x h3
              show False from h1 h4
        show False from h h2)

end exist


/- More on Proof Language -/

namespace proof_lang
  variable (f : Nat → Nat)
  variable (h : ∀ x, f x ≤ f (x + 1))

  example : (f 0 ≤ f 3) :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
    show f 0 ≤ f 3 from Nat.le_trans this (h 2)

  example : f 0 ≤ f 3 :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
    show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2) 

  example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
    fun _ : f 0 ≥ f 1 =>
    fun _ : f 1 ≥ f 2 =>
    have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1› 
    have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
    show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
end proof_lang