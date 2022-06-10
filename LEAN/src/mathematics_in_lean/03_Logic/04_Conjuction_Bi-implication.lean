import data.real.basic
import data.nat.prime

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption},
  intro h,
  apply h₁,
  rw h,
end

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  have h : x ≠ y,
  { contrapose! h₁,
    rw h₁ },
  exact ⟨h₀, h⟩
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h1 h2,
  contrapose! h2,
  from le_antisymm h1 h2,
end

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
begin 
  cases h with h1 h2,
  split,
  { exact h1,},
  { contrapose! h2,
    exact nat.dvd_antisymm h1 h2},
end

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  rintros ⟨z, xltz, zlty⟩,
  from lt_trans xltz zlty,
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin 
  split,
    contrapose!,
    intro h',
    from le_of_eq h'.symm,

    contrapose!,
    from le_antisymm h,
end

example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
begin
  split,
  { rintros ⟨h1, h2⟩,
    split,
    { from h1,},
    { contrapose! h2,
      from le_of_eq h2.symm,},
  },
  { rintros ⟨h1, h2⟩,
    split,
    { from h1,},
    { contrapose! h2,
      from le_antisymm h1 h2,},
  },
end

theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { apply le_antisymm,
    { apply le_of_not_gt,
      intro hn,
      have : x^2 + y^2 > y^2 := by linarith,
      have : 0 > y^2 := by linarith,
      have : 0 ≤ y^2 := by apply pow_two_nonneg,
      linarith,},
    { apply pow_two_nonneg,}
  },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin 
  split,
  { intro h,
    split,
    from aux h,
    rw add_comm at h,
    from aux h,
  },
  { rintro ⟨h1, h2⟩,
    rw [h1, h2],
    norm_num,
  },
end

example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith,
end

theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

example : ¬ monotone (λ x : ℝ, -x) :=
begin 
  rw not_monotone_iff,
  use [1, 2],
  norm_num,
end


section
variables {α : Type*} [partial_order α]
variables a b : α

example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
  { rintro ⟨h1 , h2⟩,
    split,
    from h1,
    intro h,
    apply h2,
    from le_of_eq h.symm,
  },
  { rintro ⟨h1, h2⟩,
    split,
    from h1,
    contrapose! h2,
    from le_antisymm h1 h2,
  },
end

end


section
variables {α : Type*} [preorder α]
variables a b c : α

example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  rintro ⟨h, hn⟩,
  from hn h,
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le], -- ⊢ ⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  rintros ⟨aleb, nblea⟩ ⟨blec, ncleb⟩,
  split,
  from le_trans aleb blec,
  contrapose! ncleb,
  from le_trans ncleb aleb,
end

end