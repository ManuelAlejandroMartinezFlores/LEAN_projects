import topology.metric_space.basic

section
variables {α : Type*} [partial_order α]
variables x y z : α

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬ x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
lt_iff_le_and_ne

end

section
variables {α : Type*} [lattice α]
variables x y z : α

#check x ⊓ y -- inf ⊓ 
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y --sup ⊔ 
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right: y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)


example : x ⊓ y = y ⊓ x := 
begin 
  have h : ∀ (a b : α), a ⊓ b ≤ b ⊓ a := by
  { intros,
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left,},
  apply le_antisymm,
  repeat {apply h},
end

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := 
begin 
  apply le_antisymm,
  { show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z),
    apply le_inf,
    { show x ⊓ y ⊓ z ≤ x, 
      have h' : x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left,
      have : x ⊓ y ≤ x := by apply inf_le_left,
      apply le_trans h' this,},
    { show x ⊓ y ⊓ z ≤ y ⊓ z,
      apply le_inf,
      { show x ⊓ y ⊓ z ≤ y,
        have h' : x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left,
        have : x ⊓ y ≤ y := by apply inf_le_right,
        apply le_trans h' this,},
      { show x ⊓ y ⊓ z ≤ z,
        apply inf_le_right,},},},
  { show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z,
    apply le_inf,
    { show x ⊓ (y ⊓ z) ≤ x ⊓ y,
      apply le_inf,
      { show x ⊓ (y ⊓ z) ≤ x,
        apply inf_le_left,},
      { show x ⊓ (y ⊓ z) ≤ y,
        have h' : x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right,
        have : y ⊓ z ≤ y := by apply inf_le_left,
        apply le_trans h' this,}},
    { show x ⊓ (y ⊓ z) ≤ z,
      have h' : x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right,
      have : y ⊓ z ≤ z := by apply inf_le_right,
      apply le_trans h' this,},},
end

example : x ⊔ y = y ⊔ x := 
begin 
  apply le_antisymm,
  repeat {
    apply sup_le,
    apply le_sup_right,
    apply le_sup_left,
  }
end

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := 
begin 
  apply le_antisymm,
  { apply sup_le,
    { apply sup_le,
      { apply le_sup_left,},
      { apply le_trans,
        show y ≤ y ⊔ z; apply le_sup_left,
        apply le_sup_right,},
      },
    { apply le_trans,
      show z ≤ y ⊔ z; apply le_sup_right,
      apply le_sup_right,},},
  { apply sup_le,
    { apply le_trans,
      show x ≤ x ⊔ y; apply le_sup_left,
      apply le_sup_left,},
    { apply sup_le,
      { apply le_trans,
        show y ≤ x ⊔ y; apply le_sup_right,
        apply le_sup_left,},
      { apply le_sup_right,},},},
end

theorem absorb1 : x ⊓ (x ⊔ y) = x := 
begin
  apply le_antisymm,
  { show x ⊓ (x ⊔ y) ≤ x,
    apply inf_le_left,
    },
  { show x ≤ x ⊓ (x ⊔ y),
    apply le_inf,
    apply le_refl,
    apply le_sup_left,},
end


theorem absorb2 : x ⊔ (x ⊓ y) = x := 
begin 
  apply le_antisymm,
  { show x ⊔ (x ⊓ y) ≤ x,
    apply sup_le,
    apply le_refl,
    apply inf_le_left,},
  { show x ≤ x ⊔ (x ⊓ y),
    apply le_sup_left,},
end

end

section

variables {α : Type*} [distrib_lattice α]
variables x y z : α

#check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

end 

section
variables {α : Type*} [lattice α]
variables a b c : α

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
begin
  have h' : (a ⊔ b) ⊓ (a ⊔ c) = a ⊔ ((a ⊔ b) ⊓ c) :=
    calc
      (a ⊔ b) ⊓ (a ⊔ c) = ((a ⊔ b) ⊓ a) ⊔ ((a ⊔ b) ⊓ c) : by apply h
      ... = a ⊔ ((a ⊔ b) ⊓ c) : by rw [inf_comm, inf_sup_self],
  have h'' : (a ⊔ b) ⊓ (a ⊔ c) = a ⊔ (c ⊓ a) ⊔ (c ⊓ b) :=
    calc 
      (a ⊔ b) ⊓ (a ⊔ c) = a ⊔ ((a ⊔ b) ⊓ c) : by apply h'
      ... = a ⊔ ((c ⊓ a) ⊔ (c ⊓ b)) : by rw [inf_comm, h]
      ... = a ⊔ (c ⊓ a) ⊔ (c ⊓ b) : by rw [sup_assoc],
  rw h'',
  apply symm,
  calc 
    a ⊔ (c ⊓ a) ⊔ (c ⊓ b) = a ⊔ (a ⊓ c) ⊔ (c ⊓ b) : by rw inf_comm
    ... = a ⊔ (c ⊓ b) : by rw sup_inf_self
    ... = a ⊔ (b ⊓ c) : by rw inf_comm,
end

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
begin 
  apply symm,
  calc 
    (a ⊓ b) ⊔ (a ⊓ c) = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c) : by rw h
    ... = (a ⊔ (a ⊓ b)) ⊓ ((a ⊓ b) ⊔ c) : by rw sup_comm 
    ... = a ⊓ (c ⊔ (a ⊓ b)) : by rw [sup_inf_self, sup_comm]
    ... = a ⊓ (c ⊔ a) ⊓ (c ⊔ b) : by rw [h, inf_assoc]
    ... = a ⊓ (b ⊔ c) : by rw [sup_comm, inf_sup_self, sup_comm], 
end

end


section

variables {R : Type*} [ordered_ring R]
variables a b c : R

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)


lemma aux1 : a ≤ b → 0 ≤ b - a := 
begin 
  intro h,
  have : -a + a ≤ -a + b := add_le_add_left h (-a),
  have : a + -a ≤ b + -a := by rw [add_comm (-a), add_comm (-a)] at this; exact this,
  rw [add_neg_self] at this,
  rw tactic.ring.add_neg_eq_sub at this,
  exact this,
end


lemma aux2 : 0 ≤ b - a → a ≤ b := 
begin 
  intro h,
  have : a + 0 ≤ a + (b - a) := add_le_add_left h a,
  have : a ≤ (a + b) + -a := 
    by rw [add_zero, ←tactic.ring.add_neg_eq_sub, ←add_assoc] at this; exact this,
  rw add_neg_cancel_comm at this,
  exact this,
end


example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := 
begin 
  have : 0 ≤ (b - a) * c := by
  { apply mul_nonneg, 
    exact aux1 a b h,
    exact h',},
  have : 0 ≤ (b * c) - (a * c) := by rw [sub_mul] at this; exact this,
  exact aux2 (a*c) (b*c) this,
end

end



section 

variables {X : Type*} [metric_space X]
variables x y z : X

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)


example (x y : X) : 0 ≤ dist x y := 
begin 
  have : dist x x ≤ dist x y + dist y x := by apply dist_triangle,
  have : 0 ≤ dist x y + dist x y := by rw [dist_self, dist_comm y x] at this; exact this,
  have : 0 ≤ 2 * dist x y := by rw [←two_mul] at this; exact this,
  exact nonneg_of_mul_nonneg_left this (by norm_num),
end

#check nonneg_of_mul_nonneg_left

end