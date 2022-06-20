import data.nat.gcd
import data.real.irrational
import tactic



#print nat.coprime 

example (m n : nat) (h : m.coprime n) : m.gcd n = 1 := h 

example : nat.coprime 12 7 := by norm_num
example : nat.gcd 12 8 = 4 := by norm_num


#check @nat.prime_def_lt

example (p : ℕ) (prime_p : nat.prime p) : 2 ≤ p ∧ ∀ (m : ℕ), m < p → m ∣ p → m = 1 :=
by rwa nat.prime_def_lt at prime_p

#check @nat.prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : nat.prime p) : ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p :=
prime_p.eq_one_or_self_of_dvd

example : nat.prime 17 := by norm_num

-- commonly used
example : nat.prime 2 := nat.prime_two
example : nat.prime 3 := nat.prime_three



#check @nat.prime.dvd_mul
#check @nat.prime.dvd_mul 
#check nat.prime_two.dvd_mul

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
begin
  rw [pow_two, nat.prime_two.dvd_mul] at h,
  cases h; assumption,
end

example {m n : ℕ} (coprime_mn : m.coprime n) : m^2 ≠ 2 * n^2 :=
begin
  intro sqreq,
  have : 2 ∣ m,
    apply even_of_even_sqr,
    use [n^2, sqreq],
  
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,

  have : 2 * (2 * k^2) = 2 * n^2,
    rw [←sqreq, meq], ring,

  have : 2 * k^2 = n^2,
    apply (mul_right_inj' _).mp,
    from this, norm_num,
  
  have : 2 ∣ n,
    apply even_of_even_sqr,
    use [k^2, this.symm],

  have : 2 ∣ m.gcd n,
    apply (dvd_gcd_iff 2 m n).mpr,
    split, assumption',
  
  have : 2 ∣ 1,
    convert this,
    from (nat.coprime_iff_gcd_eq_one.mp coprime_mn).symm,
  
  norm_num at this,
end


lemma dvd_of_dvd_sq {p m : ℕ} (pp : p.prime) (h : p ∣ m^2) : p ∣ m := 
begin 
  rw [pow_two, nat.prime.dvd_mul pp] at h,
  cases h, assumption',
end

example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin 
  intro heq,
  have : p ∣ m,
    apply dvd_of_dvd_sq prime_p,
    use [n^2, heq],

  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,

  have : p * (p * k^2) = p * n^2,
    rw [←heq, meq], ring,

  have : p * k^2 = n^2,
    apply (mul_right_inj' _).mp,
    from this, exact nat.prime.ne_zero prime_p,

  have : p ∣ n,
    apply dvd_of_dvd_sq prime_p,
    use [k^2, this.symm],

  have : p ∣ m.gcd n,
    apply (dvd_gcd_iff p m n).mpr,
    split, assumption',

  have : p ∣ 1,
    convert this,
    rw nat.coprime_iff_gcd_eq_one.mp,
    assumption,
  
  from nat.prime.not_dvd_one prime_p this,
end


#check nat.factors
#check nat.prime_of_mem_factors
#check nat.prod_factors
#check nat.factors_unique


#check @nat.factors_prime
#eval (12 : ℕ).factors.count 2 -- 2


theorem nat.count_factors_mul_of_pos (m n p : ℕ) (mpos : 0 ≠ m) (npos : 0 ≠ n) :
  (m * n).factors.count p = m.factors.count p + n.factors.count p :=
begin 
  dsimp,
  repeat {rw nat.factors_count_eq,},
  rw nat.factorization_mul,
    refl,
    from mpos.symm,
    from npos.symm,
end

theorem nat.factors_count_pow (n k p : ℕ) : (n^k).factors.count p = k * n.factors.count p :=
begin 
  repeat {rw nat.factors_count_eq,},
  rw nat.factorization_pow,
  refl,
end

theorem nat.prime_one_factor (p : ℕ) (prime_p : p.prime) : p.factors.count p = 1 :=
begin 
  rw nat.factors_prime prime_p,
  simp,
end

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin
  intro heq,
  have nsq_nez : n^2 ≠ 0,
    by simpa,
  
  have eq1 : (m^2).factors.count p = 2 * m.factors.count p,
    apply nat.factors_count_pow,

  have eq2 : (p * n^2).factors.count p = 2 * n.factors.count p + 1,
    rw nat.count_factors_mul_of_pos p (n^2),
    rw nat.prime_one_factor p prime_p,
    rw nat.factors_count_pow, linarith,
    from ne_of_lt (nat.prime.pos prime_p),
    from nsq_nez.symm,

  have : (2 * m.factors.count p) % 2 = (2 * n.factors.count p + 1) % 2,
    rw [←eq1, heq, eq2],
  
  rw [add_comm, nat.add_mul_mod_self_left, nat.mul_mod_right] at this,
  norm_num at this,
end


example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m^k = r * n^k) :
  ∀ p : ℕ, p.prime → k ∣ r.factors.count p :=
begin 
  intros p prime_p,
  cases r with r,
  { simp,},

  have npow_nz : n^k ≠ 0,
    intro npowz, from nnz (pow_eq_zero npowz),
  
  have eq1 : (m^k).factors.count p = k * m.factors.count p,
    apply nat.factors_count_pow,

  have eq2 : (r.succ * n^k).factors.count p = 
      k * n.factors.count p + r.succ.factors.count p,
    rw [nat.count_factors_mul_of_pos, nat.factors_count_pow, add_comm],
    show 0 ≠ r.succ, intro, contradiction,
    show 0 ≠ n^k, from npow_nz.symm,

  have : r.succ.factors.count p = k * m.factors.count p - k * n.factors.count p,
    rw [←eq1, pow_eq, eq2], simp,

  rw this,
  apply nat.dvd_sub',
  repeat {apply dvd_mul_right,},
end


