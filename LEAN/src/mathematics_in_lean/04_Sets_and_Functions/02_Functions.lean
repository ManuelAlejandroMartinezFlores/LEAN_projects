import data.set.lattice
import data.set.function
import analysis.special_functions.log.basic



section
variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs],},
    { right, use [x, xt]},},
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
    { use [x, or.inl xs]},
    { use [x, or.inr xt]}},
end

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
begin 
  split,
  { rintros fsv x xs,
    apply fsv,
    use [x, xs, rfl],},
  { rintros sfv y ⟨x, xs, rfl⟩,
    apply sfv,
    from xs,},
end

#check image_subset_iff

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
begin 
  rintros y ⟨x, ⟨xs, heq⟩⟩,
  rw h heq at xs,
  from xs,
end 

#check injective f 
#check surjective f

example : f '' (f⁻¹' u) ⊆ u :=
begin 
  refine image_subset_iff.mpr _,
  apply subset.refl,
end

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
begin 
  rintros y yu,
  rcases h y with ⟨x, rfl⟩,
  use x,
  split,
  from yu,
  refl,
end

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
begin 
  rintros y ⟨x, ⟨xs, fxeq⟩⟩,
  use [x, h xs, fxeq],
end

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
begin 
  intros x xu,
  apply h,
  from xu,
end

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin 
  ext x,
  split,
  { rintro (fu | fv),
    left, from fu,
    right, from fv,},
  { rintro (fu | fv),
    left, from fu,
    right, from fv,}
end

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin 
  rintros y ⟨x, ⟨⟨xs, xt⟩, fxeq⟩⟩,
  split,
  { use [x, xs, fxeq]},
  { use [x, xt, fxeq]},
end

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin 
  rintros y ⟨⟨x, ⟨xs, fxeq⟩⟩, ⟨z, ⟨zt, fzeq⟩⟩⟩,
  use x,
  split,
  { split, from xs,
    have : x = z,
      apply h,
      apply eq.trans fxeq fzeq.symm,
    rwa this.symm at zt,},
  { from fxeq,},
    
end

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin 
  rintros y ⟨fs, fnt⟩,
  rcases fs with ⟨x, ⟨xs, fxeq⟩⟩,
  use x,
  split,
  { split,
    from xs,
    contrapose! fnt,
    use [x, fnt, fxeq],},
  { from fxeq,},
end

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin 
  rintros x ⟨xu, xnv⟩,
  split; assumption,
end

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin 
  ext y,
  split,
  { rintros ⟨⟨x, ⟨xs, fxeq⟩⟩, yv⟩,
    use x,
    split,
    { split,
      from xs,
      rwa fxeq.symm at yv,},
    { from fxeq,}},
  { rintros ⟨x, ⟨⟨xs, yv⟩, fxeq⟩⟩,
    use x,
    from ⟨xs, fxeq⟩,
    rwa fxeq.symm,}
end

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
begin 
  rintros y ⟨x, ⟨xs, yu⟩, fxeq⟩,
  left,
  use [x, xs, fxeq],
end

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin 
  rintros x ⟨xs, fxu⟩,
  split,
  { use [x, xs, rfl],},
  { from fxu,}
end

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin 
  rintros x (xs | fxu),
  { left,
    use [x, xs, rfl],},
  { right,
    use fxu,} 
end


variables {I : Type*} (A : I → set α) (B : I → set β)

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq],},
  { rintros ⟨i, x, ⟨xAi, fxeq⟩⟩,
    use [x, i, xAi, fxeq],},
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, ⟨xAi, fxeq⟩⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rwa this,},
  { from fxeq,},
end

end


section 
open set real

example : inj_on log { x | x > 0 } :=
begin
  intros x xpos y ypos e,
  calc 
    x = exp (log x) : by rw exp_log xpos
    ... = exp (log y) : by rw e
    ... = y : by rw exp_log ypos,
end

example : range exp = { y | y > 0 } :=
begin
  ext y, split,
  { rintros ⟨x, rfl⟩,
    apply exp_pos,},
  { intro ypos,
    use log y,
    apply exp_log ypos,}
end


example : inj_on sqrt { x | x ≥ 0 } :=
begin 
  intros x xge y yge e,
  calc 
    x = (sqrt x) ^ 2 : by rw sq_sqrt xge
    ... = (sqrt y) ^ 2 : by rw e
    ... = y : by rw sq_sqrt yge,
end

#check sqrt_sq

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
begin 
  intros x xge y yge,
  dsimp, intro e,
  calc 
    x = sqrt (x ^ 2) : by rw sqrt_sq xge
    ... = sqrt (y ^ 2) : by rw e
    ... = y : by rw sqrt_sq yge,
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin 
  ext y, dsimp, split,
  { rintro ⟨x, xge, fxeq⟩,
    rw ←fxeq,
    apply sqrt_nonneg,},
  { intro yge,
    use y^2,
    dsimp,
    split,
    apply sq_nonneg,
    rw sqrt_sq yge,}
end

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
begin 
  ext y, split,
  { rintro ⟨x, fxeq⟩,
    dsimp at fxeq,
    dsimp, rw ←fxeq,
    apply sq_nonneg,},
  { dsimp, intro yge,
    use sqrt y,
    dsimp,
    rw sq_sqrt yge,},
end


end




section 
variables {α β : Type*} [inhabited α]

#check (default : α)

variables (P : α → Prop) (h : ∃ x, P x)

#check classical.some h

example : P (classical.some h) := classical.some_spec h


noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end


variable  f : α → β
open function

example : injective f ↔ left_inverse (inverse f) f  :=
begin 
  split,
  { intros injf x,
    apply injf,
    apply inverse_spec,
    use x,},
  { intros lfi x y e,
    calc 
      x = inverse f (f x) : by rw lfi
      ... = inverse f (f y) : by rw e
      ... = y : by rw lfi,},
end

example : surjective f ↔ right_inverse (inverse f) f :=
begin 
  split,
  { intros surf y,
    apply inverse_spec,
    use surf y,},
  { rintros rfi y,
    use (inverse f) y,
    from rfi y,}
end

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surf,
  let S := { i | i ∉ f i},
  rcases surf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
    intro h',
    have : j ∉ f j,
      by rwa h at h',
    contradiction,
  have h₂ : j ∈ S,
    from h₁,
  have h₃ : j ∉ S,
    rwa h at h₁,
  contradiction,
end

end
