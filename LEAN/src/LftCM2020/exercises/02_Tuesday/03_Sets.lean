import data.set.basic data.set.lattice data.nat.parity
import tactic.linarith

open set nat function

open_locale classical

variables {α : Type*} {β : Type*} {γ : Type*} {I : Type*}

/-!
## Set exercises
These are collected from *Mathematics in Lean*.
We will go over the examples together, and then let you
work on the exercises.
There is more material here than can fit in the sessions,
but we will pick and choose as we go.
-/

section set_variables

variable  x : α
variables s t u : set α

/-!
### Notation
-/

#check s ⊆ t        -- \sub
#check x ∈ s        -- \in or \mem
#check x ∉ s        -- \notin
#check s ∩ t        -- \i or \cap
#check s ∪ t        -- \un or \cup
#check (∅ : set α)  -- \empty

/-!
### Examples
-/

-- Three proofs of the same fact.
-- The first two expand definitions explicitly,
-- while the third forces Lean to do the unfolding.

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end

-- Use `cases` or `rcases` or `rintros` with union.
-- Two proofs of the same fact, one longer and one shorter.

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  right,
  show x ∈ s ∩ u,
  exact ⟨xs, xu⟩
end

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, exact ⟨xs, xt⟩ },
  right, exact ⟨xs, xu⟩
end

-- Two examples with set difference.
-- Type it as ``\\``.
-- ``x ∈ s \ t`` expands to ``x ∈ s ∧ x ∉ t``.

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, dsimp,
  intro xtu, -- x ∈ t ∨ x ∈ u
  cases xtu with xt xu,
  { show false, from xnt xt },
  show false, from xnu xu
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

/-!
### Exercises
-/

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin 
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  from ⟨xs, or.inl xt⟩,
  from ⟨xs, or.inr xu⟩,
end

example : s \ (t ∪ u) ⊆ s \ t \ u :=
begin 
  rintros x ⟨xs, h⟩, dsimp at h,
  push_neg at h, 
  use [xs, h.1, h.2],
end

/-!
### Proving two sets are equal
-/

-- the ext tactic

example : s ∩ t = t ∩ s :=
begin
  ext x,
  -- simp only [mem_inter_eq],  -- optional.
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

/-!
### Exercises
-/

example : s ∩ (s ∪ t) = s :=
begin 
  ext x, 
  split,
  { rintros ⟨xs, h⟩, from xs,},
  { intro xs, from ⟨xs, or.inl xs⟩,}
end

example : s ∪ (s ∩ t) = s :=
begin 
  ext x, split,
  { rintro (xs | ⟨xs, xt⟩); from xs,},
  { intro xs, left, from xs,}
end

example : (s \ t) ∪ t = s ∪ t :=
begin 
  ext x, split,
  { rintro (⟨xs, xnt⟩ | xt),
      left, from xs,
      right, from xt,},
  { rintro (xs | xt), 
    { by_cases xt : x ∈ t, 
      right, from xt,
      left, from ⟨xs, xt⟩,},
    right, from xt,}
end

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin 
  ext x, split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩), 
    { simp, split, left, from xs,
      intro, from xnt,},
    { simp, split, right, from xt,
      intro, contradiction,} },
  { simp, rintros (xs | xt) xsnt,
    { use [xs, xsnt xs],},
    { by_contra' h',
      from xsnt (h'.2 xt) xt,}} 
end

/-!
### Set-builder notation
-/

def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em
end

example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := rfl
example : (∅ : set α) = {x | false} := rfl
example : (univ : set α) = {x | true} := rfl

example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial

/-!
### Exercise
-/

-- Use `intro n` to unfold the definition of subset,
-- and use the simplifier to reduce the
-- set-theoretic constructions to logic.
-- We also recommend using the theorems
-- ``prime.eq_two_or_odd`` and ``even_iff``.

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin 
  rintros n ⟨np, n2⟩ en, dsimp at *, 
  cases prime.eq_two_or_odd np,
  linarith,
  rw even_iff at en,
  linarith,
end

/-!
Indexed unions
-/

-- See *Mathematics in Lean* for a discussion of
-- bounded quantifiers, which we will skip here.

section

-- We can use any index type in place of ℕ
variables A B : ℕ → set α

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end

end

/-!
### Exercise
-/

-- One direction requires classical logic!
-- We recommend using ``by_cases xs : x ∈ s``
-- at an appropriate point in the proof.

section

variables A B : ℕ → set α

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin 
  ext x, simp only [mem_Inter], split,
  { rintros (xs | fAi) i, 
    right, from xs,
    rw mem_Inter at fAi,
    left, from fAi i,},
  { intro h, by_cases xs : x ∈ s,
    { left, from xs,},
    { right, rw mem_Inter, intro i,
      cases h i with xAi xs,
      from xAi, 
      contradiction,}},
end

end

/-
Mathlib also has bounded unions and intersections,
`⋃ x ∈ s, f x` and `⋂ x ∈ s, f x`,
and set unions and intersections, `⋃₀ s` and `⋂₀ s`,
where `s : set α`.
See *Mathematics in Lean* for details.
-/

end set_variables

/-!
### Functions
-/

section function_variables

variable  f : α → β
variables s t : set α
variables u v : set β
variable  A : I → set α
variable  B : I → set β

#check f '' s
#check image f s
#check f ⁻¹' u    -- type as \inv' and then hit space or tab
#check preimage f u

example : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl
example : f ⁻¹' u = {x | f x ∈ u } := rfl

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs] },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end

/-!
### Exercises
-/

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
begin 
  split, 
  { intros fsc x xs,
    apply fsc, use [x, xs], },
  { rintros sfu y ⟨x, xs, fx⟩, 
    rw ←fx, apply sfu, from xs,},
end



end function_variables