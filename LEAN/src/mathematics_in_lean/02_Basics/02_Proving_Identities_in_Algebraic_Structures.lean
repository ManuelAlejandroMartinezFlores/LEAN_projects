import algebra.ring
import data.real.basic
import tactic

section 
variables (R : Type*) [ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
end

section
variables (R : Type*) [comm_ring R]
variables a b c d : R

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end
end

namespace my_ring
variables {R : Type*} [ring R]

theorem add_zero (a : R) : a + 0 = a :=
by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 :=
by rw [add_comm, add_left_neg]

#check @my_ring.add_zero
#check @add_zero

end my_ring

namespace my_ring
variables {R : Type*} [ring R]

theorem neg_add_cancel_left {a b : R} : -a + (a + b) = b :=
  by rw [←add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_right {a b : R} : (a + b) + -b = a :=
  by rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
begin
  have : -a + (a + b) = -a +(a + c) := by rw [h],
  rw [neg_add_cancel_left, neg_add_cancel_left] at this,
  exact this,
end

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
begin
  have : b + a = b + c := by rw [add_comm a b, add_comm c b, h] at h; exact h, 
  exact add_left_cancel this
end

theorem mul_zero (a : R) : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
  { rw [←mul_add, add_zero, add_zero] },
  rw add_left_cancel h
end

theorem zero_mul (a : R) : 0 * a = 0 :=
begin
  have : 0 * a + 0 * a = 0 * a + 0,
  { rw [←add_mul, add_zero, add_zero]},
  exact add_left_cancel this,
end

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
begin
  have : -a + (a + b) = -a + 0 := by rw[h],
  have : b = -a := by rw [neg_add_cancel_left, add_zero] at this; exact this,
  by rw this,
end

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
begin
  have : (a + b) + -b = 0 + -b := by rw [h],
  rw [add_neg_cancel_right, zero_add] at this, 
  exact this,
end

theorem neg_zero : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_zero
end

theorem neg_neg (a : R) : -(-a) = a :=
begin  
  have : -(-a) + -a = 0 := by rw add_left_neg,
  have : (-(-a) + -a) + a = 0 + a := by rw [this],
  have : -(-a) + (-a + a) = a := by rw [zero_add, add_assoc] at this; exact this,
  rw [add_left_neg, add_zero] at this,
  exact this
end

end my_ring




namespace my_ring

variables {R : Type*} [ring R]

theorem self_sub (a : R) : a - a = 0 :=
begin
  calc 
    a - a
        = (0 + a) - a : 
          by rw [zero_add]
    ... = 0 : 
          by rw [sub_eq_add_neg, add_neg_cancel_right]
end

lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

theorem two_mul (a : R) : 2 * a = a + a :=
begin 
  calc 
    2 * a 
        = (1 + 1) * a : by rw [one_add_one_eq_two]
    ... = a + a : by rw [add_mul, one_mul]
end

end my_ring


section
variables (A : Type*) [add_group A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)
end

section
variables {G : Type*} [group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace my_group

lemma mul_left_cancel {a b c : G} : a * b = a * c → b = c := 
begin
  intros h,
  have h : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw [h],
  have h : (a⁻¹ * a) * b = (a⁻¹ * a) * c := 
    by rw [h, ←mul_assoc, ←mul_assoc] at h; exact h,
  have : 1 * b = 1 * c := 
    by rw [h, mul_left_inv] at h; exact h,
  rw [one_mul, one_mul] at this,
  exact this,
end



theorem mul_right_inv {a : G} : a * a⁻¹ = 1 :=
begin
  have : (a * a⁻¹)⁻¹ * ((a * a⁻¹) * (a * a⁻¹)) = 1 := 
    by rw [mul_assoc, ←mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv],
  rw [←this, ←mul_assoc, mul_left_inv, one_mul],
end

theorem mul_one {a : G} : a * 1 = a :=
begin
  calc 
    a * 1
        = a * (a⁻¹ * a) : by rw [mul_left_inv]
    ... = (a * a⁻¹) * a : by rw [mul_assoc]
    ... = a : by rw [mul_right_inv, one_mul]
end

lemma mul_right_cancel {a b c : G} : a * c = b * c → a = b := 
begin
  intros h,
  have : (a * c) * c⁻¹ = (b * c) * c⁻¹ := by rw [h],
  have : a * (c * c⁻¹) = b * (c * c⁻¹) :=
    by rw [mul_assoc, mul_assoc] at this; exact this,
  have : a * 1 = b * 1 :=
    by rw [mul_right_inv] at this; exact this,
  rw [mul_one, mul_one] at this; exact this,
end


theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin 
  have : b⁻¹ * a⁻¹ = (a * b)⁻¹,
    calc 
      b⁻¹ * a⁻¹ 
          = (a * b)⁻¹ * (a * b) * (b⁻¹ * a⁻¹) : 
            by rw [←one_mul (b⁻¹ * a⁻¹), ←mul_left_inv (a * b), mul_left_inv, one_mul, one_mul]
      ... = (a * b)⁻¹ * (a * (b * (b⁻¹ * a⁻¹))) : 
        by rw [mul_assoc, mul_assoc]
      ... = (a * b)⁻¹ * a * (b * b⁻¹) * a⁻¹ : 
        by simp only [mul_assoc]
      ... = (a * b)⁻¹ * (a * a ⁻¹) :
        by simp only [mul_right_inv, mul_one, mul_assoc]
      ... = (a * b)⁻¹ :
        by simp only [mul_right_inv, mul_one],
  rw [this],
end


end my_group
end

