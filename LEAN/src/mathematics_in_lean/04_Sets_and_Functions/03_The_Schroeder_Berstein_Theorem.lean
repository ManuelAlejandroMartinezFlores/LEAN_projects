import data.set.lattice
import data.set.function
import tactic

open set
open function

noncomputable theory
open_locale classical

variables {α β : Type*} [nonempty β]
variables (f : α → β) (g : β → α)
variables (x : α) (y : β)


#check (inv_fun g : α → β)

#check (left_inverse_inv_fun : injective g → left_inverse (inv_fun g) g)
#check (left_inverse_inv_fun : injective g → ∀ y, inv_fun g (g y) = y)

#check (inv_fun_eq : (∃ y, g y = x) → g (inv_fun g x) = x)


def sb_aux : ℕ → set α
| 0 := univ \ (g '' univ)
| (n + 1) := g '' (f '' sb_aux n)


def sb_set := ⋃ n, sb_aux f g n

def sb_fun (x : α) : β := if x ∈ sb_set f g then f x else inv_fun g x

theorem sb_right_inv {x : α} (hx : x ∉ sb_set f g) :
    g (inv_fun g x) = x :=
begin
  have : x ∈ g '' univ,
    contrapose! hx,
    rw [sb_set, mem_Union],
    use [0],
    rw [sb_aux, mem_diff],
    split,
    apply mem_univ,
    from hx,
  
  have : ∃ y, g y = x,
    simp at this,
    from this,
  
  apply inv_fun_eq,
  from this,

end


theorem sb_injective (hf: injective f) (hg : injective g) :
  injective (sb_fun f g) :=
begin
  set A := sb_set f g with A_def,
  set h := sb_fun f g with h_def,
  intros x₁ x₂ hxeq,
  show x₁ = x₂,
    simp only [h_def, sb_fun, ←A_def] at hxeq,
    by_cases xA : x₁ ∈ A ∨ x₂ ∈ A,

    { wlog : x₁ ∈ A := xA using [x₁ x₂, x₂ x₁],
      have x₂A : x₂ ∈ A,
        apply not_imp_self.mp,
        assume x₂nA : x₂ ∉ A,
        rw [if_pos xA, if_neg x₂nA] at hxeq,
        rw [A_def, sb_set, mem_Union] at xA,
        have x₂eq : x₂ = g (f x₁),
          calc 
            x₂ = g (inv_fun g x₂) : by rw sb_right_inv f g x₂nA
            ... = g (f x₁) : by rw hxeq,
        rcases xA with ⟨n, hn⟩,
        rw [A_def, sb_set, mem_Union],
        use n + 1,
        simp [sb_aux],
        use [x₁, hn, x₂eq.symm],
      
      rw [if_pos xA, if_pos x₂A] at hxeq,
      from hf hxeq,},
    { push_neg at xA,
      rw [if_neg xA.1, if_neg xA.2] at hxeq,
      calc
        x₁ = g (inv_fun g x₁) : by rw sb_right_inv f g xA.1
        ... = g (inv_fun g x₂) : by rw hxeq
        ... = x₂ : by rw sb_right_inv f g xA.2,},
end

theorem sb_surjective (hf: injective f) (hg : injective g) :
  surjective (sb_fun f g) :=
begin 
  set A := sb_set f g with A_def,
  set h := sb_fun f g with h_def,
  intro y,
  by_cases gyA : g y ∈ A,
  { rw [A_def, sb_set, mem_Union] at gyA,
    rcases gyA with ⟨n, hn⟩,
    cases n with n,
    { simp [sb_aux] at hn,
      contradiction,},
    { simp [sb_aux] at hn,
      rcases hn with ⟨x, xmem, hx⟩,
      use x,
      have : x ∈ A,
        rw [A_def, sb_set, mem_Union],
        use [n, xmem],
      simp only [h_def, sb_fun, if_pos this],
      from hg hx,}},
  { rw [A_def] at gyA,
    use g y,
    rw [h_def, sb_fun, if_neg gyA],
    apply left_inverse_inv_fun,
    from hg,}
end


theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf: injective f) (hg : injective g) :
  ∃ h : α → β, bijective h := 
⟨sb_fun f g, sb_injective f g hf hg, sb_surjective f g hf hg⟩