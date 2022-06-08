import data.real.basic

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε


lemma my_lemma : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  calc
    abs (x * y) = abs x * abs y : by rw abs_mul
    ... ≤ abs x * ε             : 
      mul_le_mul (le_of_eq (eq.refl (abs x))) (le_of_lt ylt) (abs_nonneg y) (abs_nonneg x)
    ... < 1 * ε                 : 
      (mul_lt_mul_right epos).mpr (lt_of_lt_of_le xlt ele1)
    ... = ε                     : one_mul ε
end


section
variables (f g : ℝ → ℝ) (a b : ℝ)


def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
begin 
  intro x,
  dsimp,
  apply add_le_add,
  apply hfa,
  apply hgb,
end


example (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
begin 
  intro x,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb,
end

example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
  fn_lb (λ x, f x * g x) 0 :=
begin 
  intro x,
  change 0 ≤ f x * g x,
  apply mul_nonneg,
  apply nnf,
  apply nng,
end

example (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) :=
begin 
  intro x,
  change f x * g x ≤ a * b,
  apply mul_le_mul,
  apply hfa,
  apply hfb,
  apply nng,
  exact nna,
end

end


section
variables {α : Type*} {R : Type*} [ordered_cancel_add_comm_monoid R]

#check @add_le_add

def fn_ub' (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

theorem fn_ub_add {f g : α → R} {a b : R}
    (hfa : fn_ub' f a) (hgb : fn_ub' g b) :
  fn_ub' (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

end

section
example (f : ℝ → ℝ) (h : monotone f) :
  ∀ {a b}, a ≤ b → f a ≤ f b := h


variables (f g : ℝ → ℝ)

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  dsimp,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb,
end


example {c : ℝ} (mf : monotone f) (nnc : 0 < c) :
  monotone (λ x, c * f x) :=
begin 
  intros a b aleb,
  dsimp,
  apply (mul_le_mul_left nnc).mpr,
  apply mf aleb,
end 

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
λ a b aleb, mf (mg aleb)


end



section 
variables (f g : ℝ → ℝ)
def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : fn_even f) (eg : fn_even g) : fn_even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                    ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
begin 
  intro x,
  dsimp,
  rw [of, og],
  apply neg_mul_neg,
end

example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
begin  
  intro x,
  dsimp,
  rw [ef, og],
  apply mul_neg,
end

example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
begin 
  intro x,
  dsimp,
  rw [ef, og],
  rw neg_neg,
end


end



/- Sets -/

section 
variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

theorem subset.refl : s ⊆ s := λ x xs, xs

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
begin 
  intros rs st x xin,
  apply st,
  apply rs,
  exact xin,
end

end


section
variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
begin 
  intros x xs,
  apply le_trans,
  apply h,
  apply xs,
  exact h',
end

end



section
open function

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  exact (add_left_inj c).mp h',
end

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
begin
  intros a b,
  dsimp,
  intro heq,
  cases (mul_eq_mul_left_iff.mp heq),
  { assumption,},
  { contradiction,} 
end

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) :=
begin 
  intros a b,
  dsimp,
  intro heq,
  apply injf,
  apply injg,
  exact heq,
end

end
