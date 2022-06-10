import data.real.basic

variables {x y : ℝ}

example (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }


example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h,
    from or.inl h,
  },
  { rw abs_of_neg h,
    intro h,
    from or.inr h,
  },
end

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ |x| :=
begin 
  cases le_or_gt 0 x with h h,
  { rw abs_of_nonneg h,
  },
  { rw abs_of_neg h,
    apply le_of_lt,
    apply lt_trans h,
    rw neg_pos,
    from h,
  }
end

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| :=
begin 
  cases le_or_gt 0 x with h h,
  { rw abs_of_nonneg h,
    apply le_trans,
    rw neg_nonpos,
    repeat {from h},
  },
  { rw abs_of_neg h,
  },
end

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| :=
begin 
  cases le_or_gt 0 (x + y) with h h,
  { rw abs_of_nonneg h,
    apply add_le_add; apply le_abs_self,
  },
  {
    rw abs_of_neg h,
    rw neg_add,
    apply add_le_add; apply neg_le_abs_self,
  },
end

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y :=
begin 
  split,
  { intro h,
    cases le_or_gt 0 y with h' h',
    { rw abs_of_nonneg h' at h,
      left, from h,
    },
    { rw abs_of_neg h' at h,
      right, from h,
    },
  },
  { intro h,
    cases h with hy hny,
    { apply lt_of_lt_of_le,
      from hy,
      apply le_abs_self,
    },
    { apply lt_of_lt_of_le,
      from hny,
      apply neg_le_abs_self,
    },
  },
end

theorem abs_lt : |x| < y ↔ - y < x ∧ x < y :=
begin 
  split,
  { intro h,
    cases le_or_gt 0 x with h' h',
    { rw abs_of_nonneg h' at h,
      split; linarith,
    },
    { rw abs_of_neg h' at h,
      split; linarith,
    }
  },
  { intro h,
    cases le_or_gt 0 x with h' h',
    { rw abs_of_nonneg h',
      from h.right,
    },
    { rw abs_of_neg h',
      linarith,
    }
  }

end

end my_abs



example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end


example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right,
  },
  { rw [mul_comm, mul_assoc],
    apply dvd_mul_right,
  }
end


example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
by {rcases h with ⟨x, y, rfl | rfl⟩; linarith [sq_nonneg x, sq_nonneg y],}


example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin 
  have : (x - 1) * (x + 1) = 0 := by linarith,
  have : x - 1 = 0 ∨ x + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero this,
  cases this,
    left, linarith,
    right, linarith,
end

example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
begin 
  have : (x - y) * (x + y) = 0 := by linarith,
  have : x - y = 0 ∨ x + y = 0 := eq_zero_or_eq_zero_of_mul_eq_zero this,
  cases this,
    left, linarith,
    right, linarith,
end


example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end


example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin 
  split,
  { intro hp,
    by_cases P,
    { right,
      from hp h,
    },
    { left,
      assumption,
    },
  },
  { rintros (hnp | hq) hp,
    { contradiction,
    },
    { from hq
    }
  }
end