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


namespace Nat 

  inductive Tric  (x y: Nat) where 
  | eq : x = y → Tric x y
  | gt : (z : Nat) → (x = y + z ∧ z ≠ 0) → Tric x y
  | lt : (z : Nat) → (y = x + z ∧ z ≠ 0) → Tric x y
  
  def e : 3 = 3 := by rfl
  #check Tric.eq e -- Tric 3 3

  def g : 5 = 3 + 2 ∧ 2 ≠ 0 := by 
    constructor <;> simp  

  #check Tric.gt 2 g -- Tric 5 3
  #check g 


  theorem tric_addition : ∀ (x y : Nat), Tric x y := by 
    intro x y
    induction x with  
    | zero => match y with 
      | zero => apply Tric.eq; rfl 
      | succ y => 
        have : succ y = 0 + succ y ∧ succ y ≠ 0 := by 
          constructor <;> simp  
        exact Tric.lt (succ y) this
    | succ x ih => match ih with 
      | Tric.eq e => 
        have : succ x = y + 1 ∧ 1 ≠ 0 := by constructor <;> simp [e]
        exact Tric.gt 1 this
      | Tric.gt z h => 
        have : succ x = y + (z + 1) ∧ (z + 1) ≠ 0 := by constructor <;> simp_arith [h.left]
          exact Tric.gt (z + 1) this 
      | Tric.lt z (And.intro he hz) => match z with
        | zero => contradiction
        | succ n => 
          have h1 : y = succ x + n := by simp_arith [he]
          match n with 
          | zero => 
            have : succ x = y := by simp_arith [h1]
            exact Tric.eq this
          | succ n => 
            have : succ n ≠ 0 := by simp 
            exact Tric.lt (succ n) (And.intro h1 this)

  
end Nat



        
