import data.nat.prime 
import tactic.linarith

open nat 

theorem infinitude_of_primes : ∀ N : ℕ, ∃ p ≥ N, nat.prime p := 
begin
  intro N,

  let M : ℕ := factorial N + 1,
  let p := min_fac M,

  have pp : nat.prime p := 
  begin
    refine min_fac_prime _,
    have : factorial N > 0 := factorial_pos N,
    linarith
  end,

  use p, -- Existencial
  split, -- split conj 

  { by_contradiction,
    have h₁ : p ∣ factorial N + 1 := min_fac_dvd M,
    have h₂ : p ∣ factorial N := by 
    begin
      refine pp.dvd_factorial.mpr _,
      exact le_of_not_ge h
    end,
    have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,
    exact nat.prime.not_dvd_one pp h,
  },
  { exact pp,
  },

end

