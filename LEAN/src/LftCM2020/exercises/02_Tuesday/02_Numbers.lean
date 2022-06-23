import tactic
import data.real.basic
import number_theory.padics
import data.int.gcd

/-!
## Exercises about numbers and casts
-/

/-!
## First exercises
These first examples are just to get you comfortable with
`norm_num`, `norm_cast`, and friends.
-/


example : 12345 < 67890 :=
begin
  norm_num,
end

example {α : Type} [linear_ordered_field α] : 123 + 45 < 67890/3 :=
begin
  norm_num,
end

example : nat.prime 17 :=
begin
  norm_num,
end

-- prove either this or its negation!
example : ¬ 7/3 > 2 :=
begin
  norm_num,
end


example (x : ℝ) (hx : x < 50*50) : x < 25*100 :=
begin
  norm_num at *,
  assumption,
end

example (x : ℤ) (hx : (x : ℝ) < 25*100) : x < 25*100 :=
begin
  norm_cast at *,
  assumption,
end

example (x : ℤ) (hx : (x : ℝ) < 2500) : x < 25*100 :=
begin
  norm_cast at *,
  norm_num,
  assumption,
end

example (p q r : ℕ) (h : r < p - q) (hpq : q ≤ p) : (r : ℝ) < p - q :=
begin
  norm_cast at *,
  from h,
end

example (p q r : ℕ) (hr : r < p + 2 - p) : (r : ℤ) < 5 :=
begin
  norm_cast at *,
  simp at hr,
  from lt_trans hr (by norm_num : 2 < 5),
end


/-!
## Exercise 2
This comes from the development of the p-adic numbers.
`norm_cast` is very useful here, since we need to talk about values in
ℕ, ℤ, ℚ, ℚ_p, and ℤ_p.
We've done some work to get you started. You might look for the lemmas:
-/

open padic_val_rat

#check zpow_le_of_le
#check zpow_nonneg
#check of_int_multiplicity


example {p n : ℕ} (hp : p.prime) {z : ℤ} (hd : ↑(p^n) ∣ z) : padic_norm p z ≤ ↑p ^ (-n : ℤ) :=
begin
  -- This lemma will be useful later in the proof.
  -- Ignore the "inst" argument; just use `apply aux_lemma` when you need it!
  -- Note that we haven't finished it. Fill in that final sorry.
  have aux_lemma : ∀ inst, (n : ℤ) ≤ (multiplicity ↑p z).get inst,
  { intro,
    norm_cast,
    rw [← enat.coe_le_coe, enat.coe_get],
    apply multiplicity.le_multiplicity_of_pow_dvd,
    norm_cast, from hd, },

  unfold padic_norm, split_ifs with hz hz,
  { apply zpow_nonneg,
    norm_cast,
    apply zero_le,},
  { apply zpow_le_of_le,
    norm_cast, apply le_trans, from (by norm_num : 1 ≤ 2),
    apply nat.prime.two_le hp, 
    apply neg_le_neg, rw of_int_multiplicity,
    apply aux_lemma, 
    from nat.prime.ne_one hp,
    norm_cast at hz,
    }
end





/-!
## Exercise 3
This seems like a very natural way to write the theorem
"If `a` and `b` are coprime, then there are coefficients `u` and `v` such that `u*a + v*b = 1`."
But I've made a mistake! What did I do wrong? Correct the statement of the theorem and prove it.
I've started you off with a lemma that will be useful.
You might find the `specialize` tactic to be handy as well:
if you have `h : ∀ (x y : T), R x y` and `a, b : T` in the context, then
`specialize h a b` will change the type of `h` to `R a b`.
-/

example (a b : ℕ) (h : nat.coprime a b) : ∃ u v : ℤ, u * a + v * b = 1 :=
begin
  have := nat.gcd_eq_gcd_ab,
  specialize this a b, 
  unfold nat.coprime at h,
  rw h at this,
  norm_cast at this,
  use [a.gcd_a b, a.gcd_b b],
  rw this, ring,
end






/-!
## Exercise 4
We did an example together that was similar to this.
This one takes a bit more arithmetic work.
To save you some time, here are some lemmas that may be useful!
(You may not need all of them, depending on how you approach it.)
Remember you can also use `library_search` to try to find useful lemmas.
A hint: you might find it helpful to do this once you've introduced `n`.
```
have n_pos: 0 < n,
{ ... }
```
-/

#check sub_le_iff_le_add
#check add_le_add_iff_left
#check div_le_iff
#check mul_one_div_cancel
#check mul_le_mul_left


notation `|`x`|` := abs x

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- n ≥ ⌈1 / ε⌉₊

example : seq_limit (λ n : ℕ, (n+1)/n) 1 :=
begin
  intros ε epos,  
  dsimp,
  use nat.ceil (1 / ε),
  intros n nge, 

  have npos : 0 < n,
    apply lt_of_lt_of_le,
    show 0 < ⌈1 / ε⌉₊, 
      rw nat.lt_ceil,
      apply div_pos,
      norm_num, from epos,
    from nge,
  have : (0 : ℝ) ≤ (n + 1) / n - 1,
    norm_cast,
    norm_num,
    rw le_div_iff,
    norm_num, norm_cast, from npos,
    
  simp [abs_of_nonneg this], norm_cast,
  rw div_le_iff, simp [add_mul, add_comm _ (n : ℝ)], 
  calc 
    1 = ε * (1 / ε) : by { field_simp; rw div_self; from ne_of_gt epos, }
    ... ≤ ε * nat.ceil (1 / ε) : 
      by { apply mul_le_mul, apply le_refl, apply nat.le_ceil,
          apply le_of_lt, apply div_pos, norm_num, from epos, from le_of_lt epos, }
    ... ≤ ε * n : 
      by { apply mul_le_mul, apply le_refl, norm_cast, from nge, 
          norm_cast, apply nat.zero_le, from le_of_lt epos, },
  norm_cast,
  from npos,
end