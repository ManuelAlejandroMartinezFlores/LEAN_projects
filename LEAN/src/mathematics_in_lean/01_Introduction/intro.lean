import data.nat.basic
import data.nat.parity
import tactic

open nat

example : ∀ m n : ℕ, even n → even (m * n) := 
  assume m n ⟨k, (hk : n = k + k)⟩,
  have hmn : m * n = (m * k) + (m * k) := by 
    simp [hk, mul_left_comm, mul_add],
  show ∃ l, m * n = l + l,
    from Exists.intro _ hmn 

example : ∀ m n : ℕ, even n → even (m * n) := 
  λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_add]⟩  

example : ∀ m n : ℕ, even n → even (m * n) := 
begin 
  rintros m n ⟨k, hk⟩,
  -- ⊢ even (m * k)
  use m * k,
  -- ⊢ m * n = m * k + m + k
  rw hk, 
  -- ⊢ m * (k + k) = m * k + m * k
  ring -- conmutative (semi)rings
end

example : ∀ m n : ℕ, even n → even (m * n) := 
  by intros; simp * with parity_simps 



