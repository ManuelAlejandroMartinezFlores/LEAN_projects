import data.nat.prime
import algebra.big_operators
import tactic


example (n : ℕ) : n.succ ≠ 0 := n.succ_ne_zero 

example (m n : ℕ) (h : m.succ = n.succ) : m = n := nat.succ.inj h


def fac : ℕ → ℕ
| 0  := 1
| (n + 1) := (n + 1) * fac n

example : fac 0 = 1 := rfl
example : fac 0 = 1 := by rw fac
example : fac 0 = 1 := by simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := rfl
example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rw fac
example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n := 
begin 
  induction n with n ih,
  { from zero_lt_one,},
    rw fac,
    apply mul_pos,
    from n.succ_pos,
    from ih,
end


theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n :=
begin
  induction n with n ih,
  { linarith,},
    rw fac,
    cases nat.of_le_succ ile with h h,
    { apply dvd_mul_of_dvd_right, from ih h,},
      rw h,
      apply dvd_mul_right,
end

theorem pow_two_le_fac (n : ℕ) : 2^(n-1) ≤ fac n :=
begin 
  cases n with n,
  { simp [fac],},
    induction n with n ih,
    { simp [fac],},
      rw fac,
      simp, simp at ih,
      apply mul_le_mul',
      { rw nat.succ_eq_add_one,
        linarith,},
      from ih,
end


section 
variables {α : Type*} (s : finset ℕ) (f : ℕ → ℕ) (n : ℕ)



#check finset.sum s f
#check finset.prod s f

open_locale big_operators
open finset

example : s.sum f = ∑ x in s, f x := rfl
example : s.prod f = ∏ x in s, f x := rfl

example : (range n).sum f = ∑ x in range n, f x := rfl
example : (range n).prod f = ∏ x in range n, f x := rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ): ∑ x in range n.succ, f x = (∑ x in range n, f x) + f n :=
finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ): ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
finset.prod_range_succ f n


example (n : ℕ) : fac n = ∏ i in range n, (i + 1) :=
begin 
  induction n with n ih,
  { simp [fac],},
  { rw [fac, prod_range_succ, ih, mul_comm],},
end


theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 :=
begin
  symmetry, apply nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2),
  induction n with n ih,
  { simp,},
  { rw [sum_range_succ, mul_add 2, ←ih, nat.succ_eq_add_one],
    ring_nf,}
end

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 :=
begin 
  symmetry, apply nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6),
  induction n with n ih,
  { simp,},
  { rw [sum_range_succ, mul_add 6, ←ih, nat.succ_eq_add_one],
    ring,},
end

end



section 
inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat

namespace my_nat

def add : my_nat → my_nat → my_nat
| x zero     := x
| x (succ y) := succ (add x y)

def mul : my_nat → my_nat → my_nat
| x zero     := zero
| x (succ y) := add (mul x y) x

def pred : my_nat → my_nat
| zero := zero 
| (succ x) := x

def tsub : my_nat → my_nat → my_nat
| n zero := n 
| n (succ m) := tsub (n.pred) m 


theorem zero_add (n : my_nat) : add zero n = n :=
begin
  induction n with n ih,
  { refl },
  rw [add, ih]
end

theorem succ_add (m n : my_nat) : add (succ m) n = succ (add m n) :=
begin
  induction n with n ih,
  { refl },
  rw [add, ih],
  refl
end

theorem add_comm (m n : my_nat) : add m n = add n m :=
begin
  induction n with n ih,
  { rw zero_add, refl },
  rw [add, succ_add, ih]
end

theorem add_assoc (m n k : my_nat) : add (add m n) k = add m (add n k) :=
begin 
  induction k with k ih,
  { simp only [add],},
  { rw [add, ih, ←add, ←add],}
end

theorem mul_add  (m n k : my_nat) : mul m (add n k) = add (mul m n) (mul m k) :=
begin 
  induction k with k ih,
  { simp only [add, mul],},
  { rw [add, mul, ih, add_assoc, ←mul],},
end

theorem zero_mul (n : my_nat) : mul zero n = zero :=
begin 
  induction n with n ih,
  { simp [mul]},
  { rw [mul, add, ih],},
end

theorem succ_mul (m n : my_nat) : mul (succ m) n = add (mul m n) n :=
begin 
  induction n with n ih,
  { simp only [mul, add],},
  { rw [mul, ih, add, mul, add_assoc, ←add, add_comm n m, ←add, ←add_assoc],}
end

theorem mul_comm (m n : my_nat) : mul m n = mul n m :=
begin 
  induction n with n ih,
  { simp only [mul, zero_mul],},
  { rw [succ_mul, ←ih, mul],},
end

theorem succ_pred_self (n : my_nat) : n.succ.pred = n := 
begin 
  rw pred,
end


theorem sub_self (n : my_nat) : tsub n n = zero :=
begin
  induction n with n ih,
  { simp only [tsub],},
  { rw [tsub, succ_pred_self, ih],}
end

end my_nat

end
