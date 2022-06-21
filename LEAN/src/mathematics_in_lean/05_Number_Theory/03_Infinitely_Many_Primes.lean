import data.nat.prime
import algebra.big_operators
import tactic

open_locale big_operators


theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
begin 
  by_contra' h,
  interval_cases m; contradiction,
end

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
begin
  cases m, contradiction,
  cases m, contradiction,
  repeat {apply nat.succ_le_succ},
  apply zero_le,
end

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
begin
  by_contra' h,
  revert m h h0 h1,
  dec_trivial,
end

example {m : ℕ} (h : m < 2) : m = 0 ∨ m = 1 :=
  by dec_trivial!

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
  by omega


theorem exists_prime_factor {n : ℕ} (h : 2 ≤ n) :
  ∃ p : ℕ, p.prime ∧ p ∣ n :=
begin 
  by_cases np : n.prime,
  { use [n, np],},
  { induction n using nat.strong_induction_on with n ih,
    dsimp at ih,
    rw nat.prime_def_lt at np,
    push_neg at np,
    rcases np h with ⟨m, mltn, mdvdn, mne1⟩,
    have : m ≠ 0,
      intro mz,
      rw [mz, zero_dvd_iff] at mdvdn,
      linarith,
    have mgt2 : 2 ≤ m,
      from two_le this mne1,
    by_cases mp : m.prime,
    { use [m, mp, mdvdn],},
    { rcases ih m mltn mgt2 mp with ⟨k, kp, kdvdm⟩,
      use [k, kp, dvd_trans kdvdm mdvdn],},}
end


theorem primes_infinite : ∀ n, ∃ p > n, nat.prime p :=
begin
  intro n,
  have : 2 ≤ nat.factorial (n + 1) + 1,
    apply two_le,
    apply ne_of_gt, linarith,
    apply ne_of_gt, apply lt_add_of_pos_left, apply nat.factorial_pos,

  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩,
  refine ⟨p, _, pp⟩,
  show p > n,
  by_contra' ple,
  have : p ∣ nat.factorial (n + 1),
    apply nat.dvd_factorial,
    show 0 < p, from nat.prime.pos pp,
    show p ≤ n + 1, apply le_add_of_le_of_nonneg ple, norm_num,

  have : p ∣ 1,
    convert nat.dvd_sub' pdvd this,
    simp,

  show false,
    from nat.prime.not_dvd_one pp this,
end


open finset
section 


variables {α : Type*} [decidable_eq α] (r s t : finset α)

example : r ∩ (s ∪ t) ⊆ (r ∩ s) ∪ (r ∩ t) := 
begin 
  rw subset_iff,
  intro x,
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter],
  tauto,
end

example : r ∩ (s ∪ t) ⊆ (r ∩ s) ∪ (r ∩ t) :=
by { simp [subset_iff], intro x, tauto }

example : (r ∪ s) ∩ (r ∪ t) = r ∪ (s ∩ t) :=
by { ext x, simp, tauto,}

example : (r \ s \ t) = r \ (s ∪ t) :=
by { ext x, simp, tauto,}


end

example (s : finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ (∏ i in s, i) :=
  finset.dvd_prod_of_mem _ h


theorem nat.prime.eq_of_dvd_of_prime {p q : ℕ} (prime_p : p.prime) (prime_q : q.prime)
  (h : p ∣ q) : p = q := 
begin 
  cases nat.prime.eq_one_or_self_of_dvd prime_q p h with h' h',
  from absurd h' (nat.prime.ne_one prime_p),
  from h',
end

theorem mem_of_dvd_prod_primes {s : finset ℕ} {p : ℕ} (prime_p : p.prime) :
  (∀ n ∈ s, nat.prime n) → (p ∣ ∏ n in s, n) → p ∈ s := 
begin 
  intros hp hd,
  induction s using finset.induction_on with a s ans ih,
  { simp at hd,
    linarith [prime_p.two_le],},
  { simp [prod_insert ans, prime_p.dvd_mul] at hp hd,
    rw mem_insert,
    cases hd,
    { left, apply nat.prime.eq_of_dvd_of_prime,
      from prime_p, from hp.1, from hd,},
    { right, apply ih, 
      from hp.2, from hd,}}
end

example (s : finset ℕ) (x : ℕ) : x ∈ s.filter nat.prime ↔ x ∈ s ∧ x.prime :=
mem_filter

theorem primes_infinite' : ∀ (s : finset nat), ∃ p, nat.prime p ∧ p ∉ s :=
begin 
  intro s, 
  by_contra' h,
  set s' := s.filter nat.prime with s'_def,
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.prime, 
    intro n,
    simp [s'_def],
    apply h,

  have : 2 ≤ (∏ i in s', i) + 1,
     apply nat.succ_le_succ,
     apply nat.succ_le_of_lt,
     apply prod_pos,
     intros n np,
     rw mem_s' at np,
     from nat.prime.pos np,

  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩,

  have : p ∣ (∏ i in s', i),
    apply dvd_prod_of_mem,
    rw mem_s', from pp,

  have : p ∣ 1,
    convert nat.dvd_sub' pdvd this,
    simp,

  show false,
    from nat.prime.not_dvd_one pp this,

end


theorem bounded_of_ex_finset (Q : ℕ → Prop) :
  (∃ s : finset ℕ, ∀ k, Q k → k ∈ s) → (∃ n, ∀ k, Q k → k < n) := 
begin 
  rintros ⟨s, hs⟩,
  use s.sup id + 1,
  intros k Qk,
  apply nat.lt_succ_of_le,
  show id k ≤ s.sup id,
  apply le_sup,
  from hs k Qk,
end

theorem ex_finset_of_bounded (Q : ℕ → Prop) [decidable_pred Q] :
  (∃ n, ∀ k, Q k → k ≤ n) → (∃ s : finset ℕ, ∀ k, Q k ↔ k ∈ s) := 
begin 
  rintros ⟨n, hn⟩,
  use (range (n + 1)).filter Q,
  intro k,
  split,
  { intro hk,
    simp [nat.lt_succ_iff],
    from ⟨hn k hk, hk⟩,},
  { simp,}
end



example (n : ℕ) : (4 * n + 3) % 4 = 3 :=
  by { rw [add_comm, nat.add_mul_mod_self_left], norm_num}

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) :
  m % 4 = 3 ∨ n % 4 = 3 := 
begin 
  revert h,
  rw [nat.mul_mod],
  have : m % 4 < 4 := nat.mod_lt m (by norm_num),
  interval_cases  m % 4 with hm; simp [hm],
  have : n % 4 < 4 := nat.mod_lt n (by norm_num),
  interval_cases n % 4 with hn; simp [hn]; norm_num,
end

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := 
  by apply two_le; { intro neq, rw neq at h, norm_num at h}

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) :
  (n / m) ∣ n ∧ (n / m) < n := 
begin 
  have : 1 < m , apply lt_of_lt_of_le, 
    from (by norm_num : 1 < 2), from h₁,
  split,
  from nat.div_dvd_of_dvd h₀,
  apply nat.div_lt_self,
  apply lt_trans,
  show 0 < 1, norm_num,
  from lt_trans this h₂,
  from this,
end

theorem exists_prime_factor_mod_4_eq_3 {n: ℕ} (h : n % 4 = 3) :
  ∃ p : ℕ, p.prime ∧ p ∣ n ∧ p % 4 = 3 := 
begin 
  by_cases np : n.prime,
  { use [n, np, dvd_rfl, h],},

  induction n using nat.strong_induction_on with n ih,
  dsimp at ih,
  rw nat.prime_def_lt at np,
  push_neg at np,
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩,
  have mge : 2 ≤ m,
    apply two_le _ mne1,
    intro mz,
    rw [mz, zero_dvd_iff] at mdvdn, linarith,

  have neq : m * (n / m) = n := nat.mul_div_cancel' mdvdn,
  have : m % 4 = 3 ∨ (n / m) % 4 = 3,
    apply mod_4_eq_3_or_mod_4_eq_3,
    rw [neq, h],

  cases this with h' h',
  { by_cases mp : m.prime,
    { use [m, mp, mdvdn, h'],},
    { rcases ih m mltn h' mp with ⟨k, kp, kdvdm, keq⟩,
      use [k, kp, dvd_trans kdvdm mdvdn, keq],}},
  { have : (n / m) ∣ n ∧ (n / m) < n,
      from aux mdvdn mge mltn,
    by_cases nmp : (n / m).prime,
    { use [(n / m), nmp, this.1, h'],},
    { rcases ih (n /m) this.2 h' nmp with ⟨k, kp, kdvdm, keq⟩,
      use [k, kp, dvd_trans kdvdm this.1, keq],}}
end

example (m n : ℕ) (s : finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s :=
by rwa mem_erase at h

example (m n : ℕ) (s : finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s :=
by { simp at h, assumption }


theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, nat.prime p ∧ p % 4 = 3 :=
begin 
  by_contra' h,
  cases h with n hn,
  have : ∃ s : finset ℕ, ∀ p : ℕ, p.prime ∧ p % 4 = 3 ↔ p ∈ s, 
    apply ex_finset_of_bounded,
    use n,
    contrapose! hn,
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩,
    use [p, pltn, pp, p4],
  
  cases this with s hs,
  have h₀ : 2 ≤ 4 * (∏ i in erase s 3, i) + 3,
    apply two_le; norm_num,
    
  have h₁ : (4 * (∏ i in erase s 3, i) + 3) % 4 = 3,
    rw [add_comm], norm_num,

  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩,

  have ps : p ∈ s,
    rw ←hs, use [pp, p4eq],

  have pne3 : p ≠ 3,
    intro pe3,
    rw [pe3, ←nat.dvd_add_iff_left (dvd_refl 3)] at pdvd, 
    rw nat.prime_three.dvd_mul at pdvd,
    cases pdvd, norm_num at pdvd, 
    have : 3 ∈ erase s 3,
      apply mem_of_dvd_prod_primes,
      from nat.prime_three,
      intros n ns,
      simp at ns,
      from ((hs n).2 ns.2).1,
      from pdvd,
    simpa,

  have : p ∣ 4 * (∏ i in erase s 3, i),
    rw nat.prime.dvd_mul pp,
    right, apply dvd_prod_of_mem,
    simp, split; assumption,

  have : p ∣ 3, 
    convert nat.dvd_sub' pdvd this,
    simp,

  have : p = 3,
    apply nat.prime.eq_of_dvd_of_prime pp nat.prime_three this,

  contradiction,

end


