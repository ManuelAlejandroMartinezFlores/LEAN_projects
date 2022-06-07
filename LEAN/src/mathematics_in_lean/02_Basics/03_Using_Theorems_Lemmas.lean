import analysis.special_functions.log.basic 

open real
variables (a b c d e f: ℝ)

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)


variables (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)



example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin 
  apply le_trans,
  exact h₀,
  exact h₁,
end


example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin 
  apply le_trans h₀,
  exact h₁,
end


example (x : ℝ) : x ≤ x :=
  by apply le_refl


#check (le_refl  : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) :
  a < e :=
begin 
  apply lt_of_le_of_lt h₀,
  apply lt_trans h₁,
  apply lt_of_le_of_lt h₂ h₃,
end

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) :
  a < e := by linarith

example (h : 1 ≤ a) (h' : b ≤ c) :
    2 + a + exp b ≤ 3 * a + exp c :=
  by linarith [exp_le_exp.mpr h']


#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)


example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
begin 
  apply add_lt_add_right,
  apply add_lt_add_of_le_of_lt,
  { exact h₀},
  { exact exp_lt_exp.mpr h₁}
end

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add_left,
  apply exp_le_exp.mpr,
  apply add_le_add_left h₀,
end

example : (0 : ℝ) < 1 :=
by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { apply add_pos,
    norm_num,
    apply exp_pos, },
  have h₁ : 0 < 1 + exp b,
  { apply add_pos,
    norm_num,
    apply exp_pos, },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add_left,
  apply exp_le_exp.mpr h,
end

example : 0 ≤ a^2 :=
begin
  exact sq_nonneg a,
end

example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin 
  apply add_le_add_left,
  apply neg_le_neg,
  exact exp_le_exp.mpr h,
end

example : 2*a*b ≤ a^2 + b^2 :=
begin 
  have : 0 ≤ a^2 - 2*a*b + b^2,
  calc 
    a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
    ... ≥ 0 : by apply sq_nonneg,
  calc 
    2*a*b 
        = 2*a*b + 0 : by ring 
    ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) this
    ... = a^2 + b^2 : by ring,  
end

example : |a*b| ≤ (a^2 + b^2) / 2 :=
begin 
  have : 0 ≤ a^2 - 2*a*b + b^2,
  calc 
    a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
    ... ≥ 0 : by apply sq_nonneg,
  have h₀ : a*b ≤ (a^2 + b^2) / 2,
    by linarith,

  have : 0 ≤ a^2 + 2*a*b + b^2,
  calc 
    a^2 + 2*a*b + b^2 = (a + b)^2 : by ring
    ... ≥ 0 : by apply sq_nonneg,
  have h₁ : -(a*b) ≤ (a^2 + b^2) / 2,
    by linarith,

  apply abs_le'.mpr,
  constructor,
  exact h₀,
  exact h₁,
end

#check abs_le'.mpr

