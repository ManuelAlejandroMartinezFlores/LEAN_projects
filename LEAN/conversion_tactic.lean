/- Basic Navigation and Rewritting -/

namespace navrw 

  example (a b c : Nat) : a * (b * c) = a * (c * b) := by 
    conv =>
      -- ⊢ a * (b * c) = a * (c * b)
      lhs 
      -- ⊢ a * (b * c) 
      congr 
      -- ⊢ a ; ⊢ b * c
      skip 
      -- ⊢ b * c
      rw [Nat.mul_comm]

  example : (fun x : Nat => 0 + x) = (fun x : Nat => x) := by 
    conv => 
      lhs 
      -- ⊢ fun x => 0 + x
      intro x 
      -- x ⊢ 0 + x
      rw [Nat.zero_add]

end navrw

/- Pattern Matching -/

namespace pm 

  example (a b c : Nat) : a * (b * c) = a * (c * b) := by 
    conv in b * c => rw [Nat.mul_comm]

  example (a b c : Nat) : a * (b * c) = a * (c * b) := by 
    conv =>
      pattern b * c
      rw [Nat.mul_comm]

  /- Structuring -/

  example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by 
    conv => 
      lhs 
      congr 
      . rw [Nat.zero_add]
      . rw [Nat.mul_comm]

end pm 



/- Other Tactics -/

namespace ot 

  example (a b c : Nat) : a * (b * c) = a * (c * b) := by 
    conv => 
      lhs 
      arg 2 -- ⊢ b * c 
      rw [Nat.mul_comm]

  def f (x : Nat) := 
    if x > 0 then x + 1 else x + 2 

  example (g : Nat → Nat) (h1 : g x = x + 1) (h2 : x > 0) : g x = f x := by 
    conv => 
      rhs -- ⊢ f x 
      simp [f, h2] -- ⊢ x + 1
    exact h1 

  example (g : Nat → Nat → Nat) (h1 : ∀ x, x ≠ 0 → g x x = 1)
      (h2 : x ≠ 0) : g x x + x = 1 + x := by 
    conv => 
      lhs 
      arg 1 -- ⊢ g x x
      rw [h1] 
      . skip
      . tactic => exact h2 

  

end ot 