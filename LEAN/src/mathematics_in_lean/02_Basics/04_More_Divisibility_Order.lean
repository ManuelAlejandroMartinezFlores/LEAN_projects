import data.real.basic

variables (a b c d e : ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    apply min_le_right,
    apply min_le_left,},
  { show min b a ≤ min a b,
    apply le_min,
    apply min_le_right,
    apply min_le_left,},
end

#check min


example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end

example : max a b = max b a :=
begin 
  have h : ∀ (x y : ℝ), max x y ≤ max y x := by 
  { intros,
    apply max_le,
    apply le_max_right,
    apply le_max_left,},
  apply ge_antisymm,
  repeat {apply h},
end 

example : min (min a b) c = min a (min b c) :=
begin 
  apply le_antisymm,
  { apply le_min,
    { have h : min a b ≤ a := by apply min_le_left,
      have : min (min a b) c ≤ min a b := by apply min_le_left,
      show min (min a b) c ≤ a,
      apply le_trans this h,},
    { show min (min a b) c ≤ min b c,
      apply le_min,
      { have h : min a b ≤ b := by apply min_le_right,
        have : min (min a b) c ≤ min a b := by apply min_le_left,
        show min (min a b) c ≤ b,
        apply le_trans this h,},
      { show min (min a b) c ≤ c,
        apply min_le_right,},},
    },
  { apply le_min,
    { show min a (min b c) ≤ min a b,
      apply le_min,
      { show min a (min b c) ≤ a,
        apply min_le_left,},
      { show min a (min b c) ≤ b,
        have h : min b c ≤ b := by apply min_le_left,
        have : min a (min b c) ≤ min b c := by apply min_le_right,
        apply le_trans this h,},
      },
    { show min a (min b c) ≤ c,
      have h : min b c ≤ c := by apply min_le_right,
      have : min a (min b c) ≤ min b c := by apply min_le_right,
      apply le_trans this h,},
  },
end

 
lemma aux : min a b + c ≤ min (a + c) (b + c) :=
begin 
  apply le_min,
  { show min a b + c ≤ a + c,
    apply add_le_add_right,
    apply min_le_left,},
  { show min a b + c ≤ b + c,
    apply add_le_add_right,
    apply min_le_right,},
end

example : min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  { show min a b + c ≤ min (a + c) (b + c),
    apply aux,},
  { show min (a + c) (b + c) ≤ min a b + c,
    have : min (a + c) (b + c) + -c ≤ min (a + c + -c) (b + c + -c) :=
      by apply aux,
    rw [add_neg_cancel_right a c] at this,
    rw add_neg_cancel_right b at this,
    have : min (a + c) (b + c) + -c + c ≤ min a b + c := 
      by apply add_le_add_right this,
    rw [add_assoc, add_comm (-c) c, ←add_assoc, add_neg_cancel_right] at this,
    exact this,
},
end



#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)


example : |a| - |b| ≤ |a - b| :=
begin 
  have : |a| ≤ |a - b| + |b|,
    calc 
      |a| = |a - b + b| : by ring_nf
      ... ≤ |a - b| + |b| : by apply abs_add,
  linarith,
end




variables (x y z w : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

example : x ∣ x^2 :=
by apply dvd_mul_right

example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
begin 
  repeat {apply dvd_add},
  { show x ∣ y * (x * z),
    have : x ∣ (x * z) := by apply dvd_mul_right,
    apply dvd_trans,
    apply dvd_mul_right,
    exact z,
    apply dvd_mul_left,},
  { show x ∣ x^2,
    apply dvd_mul_right,},
  { show x ∣ w^2,
    apply dvd_trans h,
    apply dvd_mul_right,},
end
 

#check @dvd_trans

variables m n : ℕ
open nat

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n  : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n  : lcm 0 n = 0)


example : gcd m n = gcd n m :=
begin 
  apply gcd_greatest,
  apply gcd_dvd_right,
  apply gcd_dvd_left, 
  { show ∀ e, e ∣ n → e ∣ m → e ∣ gcd m n,
    intros e hn hm,
    apply dvd_gcd hm hn,
  },
end


#check gcd_greatest