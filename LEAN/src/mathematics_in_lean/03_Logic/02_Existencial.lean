import data.real.basic

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5/2,
  norm_num,
end

section
def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variables {f g : ℝ → ℝ}

theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

theorem fn_lb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : fn_lb f a) 
  (hgb : fn_lb g b) : fn_lb (λ x, f x + g x) (a + b) :=
begin 
  intro x,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb,
end

theorem fn_ub_mul {f g : ℝ → ℝ} {a b : ℝ} (hfa : fn_ub f a) 
  (hfb : fn_ub g b) (nng : fn_lb g 0) (nna : 0 ≤ a) :
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

example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin 
  cases ubf with a ubfa,
  cases ubg with b ubgb,
  use a + b,
  apply fn_ub_add ubfa ubgb,
end


example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin 
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  apply fn_lb_add lbfa lbgb,
end

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin 
  cases ubf with a ubfa,
  use c * a,
  intro x,
  dsimp,
  apply mul_le_mul_of_nonneg_left,
  apply ubfa,
  exact h,
end


example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin 
  rcases ubf with ⟨a, ubfa⟩,
  rcases ubg with ⟨b, ubgb⟩,
  use a + b,
  apply fn_ub_add ubfa ubgb, 
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
begin 
  rintros ⟨a, ubfa⟩ ⟨b, ubgb⟩ ,
  use a + b,
  apply fn_ub_add ubfa ubgb,
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
λ ⟨a, ubfa⟩ ⟨b, ubfb⟩, ⟨a + b, fn_ub_add ubfa ubfb⟩


end 



section
variables {α : Type*} [comm_ring α]

def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

theorem sum_of_squares_mul {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  rw [xeq, yeq],
  use [a*c - b*d, a*d + b*c],
  ring,
end

theorem sum_of_squares_mul' {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, rfl⟩,
  rcases sosy with ⟨c, d, rfl⟩,
  use [a*c - b*d, a*d + b*c],
  ring
end

end



section
variables {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  cases divab with d beq,
  cases divbc with e ceq,
  rw [ceq, beq],
  use (d * e), ring
end


example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin 
  rcases divab with ⟨d, rfl⟩,
  rcases divac with ⟨e, rfl⟩,
  use d + e,
  ring,
end

end


section
open function


example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro y,
  dsimp,
  use y - c,
  ring,
end

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro y,
  dsimp,
  use c⁻¹ * y,
  apply mul_inv_cancel_left₀,
  exact h,
end

example (x y : ℝ) (h : x - y ≠ 0) : (x^2 - y^2) / (x - y) = x + y :=
by { field_simp [h], ring }

example {f : ℝ → ℝ} (h : surjective f) : ∃ x, (f x)^2 = 4 :=
begin
  cases h 2 with x hx,
  use x,
  rw hx,
  norm_num,
end

end


section
open function
variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin 
  intro y,
  cases surjg y with b hgb,
  cases surjf b with a hfa,
  use a,
  dsimp,
  rw hfa,
  apply hgb,
end

end