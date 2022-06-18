import data.set.lattice
import data.nat.parity
import tactic



section
variable {α : Type*}
variables (s t u : set α)

open set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  from ⟨h x xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  from ⟨h x xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rintros x ⟨xs, xu⟩,
  from ⟨h xs, xu⟩,
end


example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨hs, htu⟩,
  cases htu with ht hu,
  { left,
    from ⟨hs, ht⟩,},
  { right,
    from ⟨hs, hu⟩,}
end

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨hs, ht⟩ | ⟨hs, hu⟩),
  { from ⟨hs, or.inl ht⟩,},
  { from ⟨hs, or.inr hu⟩,},
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨hs, hnt⟩, hnu⟩,
  split,
  { from hs},
  { dsimp,
    rintro (ht | hu),
    { from hnt ht,},
    { from hnu hu},}, 
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction,
end

example : s \ (t ∪ u) ⊆ s \ t \ u :=
begin 
  rintros x ⟨xs, xsu⟩,
  dsimp at xsu,
  use xs,
  intro xt,
  from xsu (or.inl xt),
  intro xu,
  from xsu (or.inr xu),
end

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩,},
  { rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩},
end

example : s ∩ t = t ∩ s :=
subset.antisymm (λ x ⟨xs, xt⟩, ⟨xt, xs⟩) (λ x ⟨xt, xs⟩, ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s :=
begin 
  ext x,
  dsimp,
  split,
  { intro xsst,
    from xsst.1,},
  { intro xs,
    from ⟨xs, or.inl xs⟩,},
end

example : s ∪ (s ∩ t) = s :=
begin 
  ext x,
  dsimp,
  split,
  { rintro (xs | ⟨xs, xt⟩);
    from xs,},
  { intro xs,
    left,
    from xs,},
end

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x,
  split,
  { rintro (⟨xs, xnt⟩ | xt),
    { from or.inl xs,},
    { from or.inr xt,},},
  { by_cases h : x ∈ t,
    { intro _,
      right,
      from h,},
    { rintro (xs | xt),
      { left,
        from ⟨xs, h⟩,},
      { contradiction,}}},
end

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin 
  ext x, split,
  { rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { split,
      { left, 
        from xs,},
      { rintro ⟨_, xt⟩,
        contradiction,},},
    { split,
      { right,
        from xt,},
      { rintro ⟨xs, xt⟩,
        contradiction,}}},
  { rintro ⟨xs | xt, xnst⟩,
    { dsimp at xnst,
      push_neg at xnst,
      left,
      from ⟨xs, xnst xs⟩,},
    { dsimp at xnst,
      push_neg at xnst,
      right,
      split,
      from xt,
      intro xs,
      from (xnst xs) xt,}},
end

def evens : set ℕ := {n | even n}
def odds : set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ := 
begin 
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em,
end

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin 
  intro n,
  dsimp,
  rintros ⟨pp, ngt⟩,
  apply nat.odd_iff_not_even.mp,
  cases nat.prime.eq_two_or_odd' pp with neq2 odn,
  linarith,
  from odn,
end

example (n : ℕ) (h : prime n) : nat.prime n :=
by rwa nat.prime_iff



end


section
variables (s t : set ℕ)

example (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  apply h₁ x xs
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ s, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x]
end

section
variable (ssubt : s ⊆ t)

include ssubt

example (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin 
  intros x xs,
  have : x ∈ t := ssubt xs,
  split,
    from h₀ x this,
    from h₁ x this,
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x :=
begin 
  rcases h with ⟨x, xs, ne, px⟩,
  use [x, ssubt xs, px],
end

end

end


section
variables {α I : Type*}
variables A B : I → set α
variable  s : set α
open set

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintro ⟨xs, ⟨i, xAi⟩⟩,
    use [i, xAi, xs],},
  { rintro ⟨i, ⟨xAi, xs⟩⟩,
    use [xs, i, xAi],},
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

open_locale classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union_eq, mem_Inter],
  split,
  { rintros (xs | xAi) i,
    right, from xs,
    left, from xAi i,},
  { rintros xsAi,
    by_cases h : x ∈ s,
    { left, from h,},
    { right, intro i,
      cases xsAi i with xAi xs,
      { from xAi,},
      { contradiction,},}},
end

def primes : set ℕ := {x | nat.prime x}

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
begin 
  ext x,
  rw mem_Union₂,
  refl,
end

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
begin 
  apply eq_univ_of_forall,
  intros x,
  rw mem_Union₂,
  dsimp,
  rcases nat.exists_infinite_primes x with ⟨p, pge, pp⟩,
  use [p, pp, pge],
end

end