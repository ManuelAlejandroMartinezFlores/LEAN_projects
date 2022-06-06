/- Quantifier identities -/

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := 
  fun h : ∃ x, r =>
    let (Exists.intro w hw) := h
      show r from hw

example (a : α) : r → (∃ x : α, r) := 
  fun h : r =>
    Exists.intro a h

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro 
    (fun h : ∃ x, p x ∧ r =>
      let (Exists.intro w (And.intro hp hr)) := h
      show (∃ x, p x) ∧ r from And.intro (Exists.intro w hp) hr)
    (fun h : (∃ x, p x) ∧ r =>
      let (Exists.intro w hw) := h.left
      show ∃ x, p x ∧ r from Exists.intro w (And.intro hw h.right))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro
    (fun h : ∃ x, p x ∨ q x =>
      let (Exists.intro w hw) := h
      Or.elim hw
        (fun hp : p w => show (∃ x, p x) ∨ (∃ x, q x) from Or.inl (Exists.intro w hp))
        (fun hq : q w => show (∃ x, p x) ∨ (∃ x, q x) from Or.inr (Exists.intro w hq)))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun hp : ∃ x, p x =>
          let (Exists.intro w hw) := hp 
          show ∃ x, p x ∨ q x from Exists.intro w (Or.inl hw))
        (fun hq : ∃ x, q x =>
          let (Exists.intro w hw) := hq
          show ∃ x, p x ∨ q x from Exists.intro w (Or.inr hw)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  Iff.intro
    (fun h : ∀ x, p x =>
      Classical.byCases
        (fun he : ∃ x, ¬ p x =>
          let (Exists.intro w hnp) := he 
          absurd (h w) hnp)
        (fun hne : ¬ (∃ x, ¬ p x) => hne))
    (fun h : ¬ (∃ x, ¬ p x) =>
      show ∀ x, p x from 
        fun x =>
          Classical.byCases
          (fun hp : p x => hp)
          (fun hnp : ¬ p x => 
            have he : ∃ x, ¬ p x := Exists.intro x hnp
            absurd he h))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=   
  Iff.intro
    (fun h : ∃ x, p x =>
      let (Exists.intro w hp) := h
      Classical.byCases
        (fun hf : ∀ x, ¬ p x =>
          absurd hp (hf w) )
        (fun hnf : ¬ (∀ x, ¬ p x) => hnf))
    (fun h : ¬ (∀ x, ¬ p x) =>
      Classical.byContradiction
        (fun hne : ¬ (∃ x, p x) =>
          have h1 : ∀ x, ¬ p x :=
            fun w =>
              fun hp : p w =>
                have he : ∃ x, p x := Exists.intro w hp
                show False from hne he
          show False from h h1))


example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
  Iff.intro
    (fun h : ¬ ∃ x, p x =>
      show ∀ x, ¬ p x from 
        (fun x =>
          fun hp : p x =>
            show False from h (Exists.intro x hp)))
    (fun h : ∀ x, ¬ p x =>
      Classical.byCases
        (fun he : ∃ x, p x =>
          let (Exists.intro w hp) := he
          absurd hp (h w))
        (fun hne : ¬ ∃ x, p x => hne))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  Iff.intro
    (fun h : ¬ ∀ x, p x =>
      Classical.byContradiction
        (fun hne : ¬ ∃ x, ¬ p x =>
          have hn : ∀ x, p x := 
            fun x => 
              Classical.byContradiction
                (fun hnp : ¬ p x =>
                  have he : ∃ x, ¬ p x := Exists.intro x hnp
                  show False from hne he)
          show False from h hn))
    (fun h : ∃ x, ¬ p x =>
      let (Exists.intro w hnp) := h
      Classical.byCases
        (fun hf : ∀ x, p x => absurd (hf w) hnp)
        (fun hnf : ¬ ∀ x, p x => hnf))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro
    (fun h : ∀ x, p x → r =>
      fun he : ∃ x, p x =>
        let (Exists.intro w hp) := he
        show r from (h w) hp)
    (fun h : (∃ x, p x) → r =>
      show ∀ x, p x → r from 
        fun x =>
          fun hp : p x => show r from h (Exists.intro x hp))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro
    (fun h : ∃ x, p x → r =>
      let (Exists.intro w hpr) := h
      fun hf : ∀ x, p x =>
        show r from hpr (hf w))
    (fun h : (∀ x, p x) → r =>
      show ∃ x, p x → r from
        Classical.byCases
          (fun hf : ∀ x, p x => 
            have hp : p a := hf a
            Exists.intro a (fun hp => (h hf)))
          (fun hnf : ¬ ∀ x, p x =>
            Classical.byContradiction
              (fun hne : ¬ ∃ x, p x → r =>
                have hf : ∀ x, p x :=
                  fun x => 
                    Classical.byContradiction
                      (fun hnp : ¬ p x =>
                        have he : ∃ x, p x → r := Exists.intro x (fun hp => absurd hp hnp)
                        show False from hne he)
                      show False from hnf hf)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  Iff.intro 
    (fun h : ∃ x, r → p x =>
      let (Exists.intro w hrpw) := h
      fun hr : r =>
        Exists.intro w (hrpw hr))
    (fun h : r → ∃ x, p x =>
      Classical.byCases
        (fun hr : r => 
          let (Exists.intro w hw) := h hr 
          Exists.intro w (fun hr => hw))
        (fun hnr : ¬ r =>
          Exists.intro a (fun hr : r => absurd hr hnr)))


/- Equivalences -/

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  Iff.intro 
    (fun h : ∀ x, p x ∧ q x =>
      show (∀ x, p x) ∧ (∀ x, q x) from And.intro
        (fun x => (h x).left)
        (fun x => (h x).right))
    (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun x => show p x ∧ q x from And.intro (h.left x) (h.right x))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  fun h : ∀ x, p x → q x =>
    fun hfp : ∀ x, p x =>
      show ∀ x, q x from
        fun x => show q x from (h x) (hfp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    fun x => Or.elim h
      (fun hfp : ∀ x, p x => show p x ∨ q x from Or.inl (hfp x))
      (fun hfq : ∀ x, q x => show p x ∨ q x from Or.inr (hfq x))


/- Component outside of Universal Quantifier -/

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := 
  fun a : α =>
    Iff.intro
      (fun h : ∀ x, r =>
        show r from h a)
      (fun h : r => show ∀ x, r from 
        fun x => h)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  Iff.intro
    (fun h : ∀ x, p x ∨ r =>
      Classical.byCases
        (fun hr : r => show (∀ x, p x) ∨ r from Or.inr hr)
        (fun hnr : ¬r => show (∀ x, p x) ∨ r from Or.inl
          fun x => Or.elim (h x)
            (fun hp : p x => hp)
            (fun hr : r => absurd hr hnr)))
    (fun h : (∀ x, p x) ∨ r =>
      fun x => 
        Or.elim h
          (fun hf : ∀ x, p x => show p x ∨ r from Or.inl (hf x))
          (fun hr : r => show p x ∨ r from Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  Iff.intro 
    (fun h : ∀ x, r → p x =>
      fun hr : r =>
        fun x => (h x) hr)
    (fun h : r → ∀ x, p x =>
      fun x =>
        fun hr : r => (h hr) x)


/- Barber Paradox -/

variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
  Classical.byCases
    (fun hb : shaves barber barber =>
      show False from ((Iff.mp (h barber)) hb) hb)
    (fun hnb : ¬ shaves barber barber =>
      show False from hnb ((Iff.mpr (h barber)) hnb))


/- Assertions -/

def even (n : Nat) : Prop := 
  ∃ x, n = 2 * x

def div (a b : Nat) : Prop :=
  ∃ x, b = a * x

def prime (n : Nat) : Prop := 
  ¬ ∃ p, p > 1 → div p n 

def infinitely_many_primes : Prop := 
  ∀ n, ∃ p, prime p → n < p

def Fermat_prime (n : Nat) : Prop :=
  prime (Nat.pow 2 (Nat.pow 2 n))

def infinitely_many_Fermat_primes : Prop := 
  ∀ n, ∃ p, Fermat_prime p → n < p

def goldbach_conjecture : Prop := 
  ∀ n, even n → n > 2 → (∃ p q, prime p → prime q → n = p + q)

def Goldbach's_weak_conjecture : Prop := 
  ∀ n, ¬ even n → n > 5 → (∃ p q r, prime p → prime q → prime r → n = p + q + r)

def Fermat's_last_theorem {n a b c : Nat}: Prop :=
  ∀ n, n > 2 → ¬ ∃ a b c, (Nat.pow a n) + (Nat.pow b n) = (Nat.pow c n)



/- Divisibility -/


example : ∀ x, div x x :=
  fun x =>
    have h : x = x * 1 := by rw [Nat.mul_one]
    Exists.intro 1 h

example (hab : div a b) (hba : div b a) (ha : a > 0) (hb : b > 0) : a = b :=
  match hab, hba with
  | (Exists.intro m hm), (Exists.intro n hn) =>
      have : a = a * (m * n) := calc
        a = b * n := by rw [hn]
        _ = a * (m * n) := by simp [hm, Nat.mul_assoc]
      have : a * 1 = a * (m * n) := (Nat.mul_one a).symm ▸ this
      have : 1 = m * n := (Nat.eq_of_mul_eq_mul_left ha this)
      sorry

example (hab : div a b) (hbc : div b c) : div a c :=
  match hab, hbc with
  | (Exists.intro m hm), (Exists.intro n hn) =>
      have hac : c = a * (m * n) := calc
        c = b * n := by rw [hn]
        _ = (a * m) * n := by rw [hm]
        _ = a * (m * n) := by simp [Nat.mul_assoc]
      show div a c from Exists.intro (m * n) hac


