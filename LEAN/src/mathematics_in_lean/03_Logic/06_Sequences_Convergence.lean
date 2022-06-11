import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
begin 
  ext x y,
  ring,
end

example (a b : ℝ) : abs a = abs (a - b + b) :=
begin 
  congr,
  ring,
end

example {a : ℝ} (h : 1 < a) : a < a * a :=
begin
  convert (mul_lt_mul_right _).2 h,
    rw one_mul,
    linarith,
end


theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin 
  intros ε epos,
  use 0,
  intros n nge,
  dsimp,
  rw [sub_self, abs_zero],
  apply epos,
end


theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε epos,
  dsimp,
  have e2pos : 0 < ε / 2 := by linarith,
  cases cs (ε / 2) e2pos with Ns fs,
  cases ct (ε / 2) e2pos with Nt ft,

  let mN := max Ns Nt,
  use mN,
  intros n nge,
  have : |s n - a| < ε / 2 := fs n (le_of_max_le_left nge),
  have : |t n - b| < ε / 2 := ft n (le_of_max_le_right nge),
  apply lt_of_le_of_lt,

  show |s n + t n - (a + b)| ≤ |s n - a| + |t n - b|,
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| : by congr; ring
    ... ≤ |s n - a| + |t n - b| : by apply abs_add,
  
  show |s n - a| + |t n - b| < ε,
  have : ε = ε / 2 + ε / 2 := by norm_num,
  rw this,
  apply add_lt_add; assumption,
end 

theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    ext,
    rw [h, zero_mul],
    rw [h, zero_mul],
  },
  { have acpos : |c| > 0,
      from abs_pos.mpr h,

    intros ε epos,
    have : ε / |c| > 0,
      from div_pos epos acpos,
    dsimp,
    cases cs (ε / |c|) this with N fn,

    use N,
    intros n nge,
    have hec : |s n - a| < ε / |c| := fn n nge,

    have hmul : |c * s n - c * a| = |c| * |s n - a|,
      calc
        |c * s n - c * a| = |c * (s n - a)| : by congr; ring
        ... = |c| * |s n - a| : by apply abs_mul,
    
    have : ε = ε * |c| / |c|,
      calc
        ε = ε * 1 : (mul_one ε).symm
        ... = ε * (|c| / |c|) : by rw div_self (ne_of_gt acpos)
        ... = ε * |c| / |c| : by ring,
    rw this,
    calc 
      |c * s n - c * a| = |c| * |s n - a| : by assumption
      ... < |c| * (ε / |c|) : by apply (mul_lt_mul_left acpos).mpr hec
      ... = ε * |c| / |c| : by ring,
  }
end

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, |a| + 1],
  intros n nge,
  have h := h n nge,
  apply lt_of_le_of_lt,

  show |s n| ≤ |a| + |s n - a|,
  calc 
    |s n| = |a + (s n - a)| : by congr; ring_nf
    ... ≤ |a| + |s n - a| : by apply abs_add,
  
  show |a| + |s n - a| < |a| + 1,
  apply add_lt_add_of_le_of_lt,
    apply le_refl,
    exact h,
end

lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
begin
  intros ε epos, dsimp,
  rcases exists_abs_le_of_converges_to cs with ⟨N, b, h⟩,
  have bpos : 0 < b,
    from lt_of_le_of_lt (abs_nonneg _) (h N (le_refl _)),
  have pos : ε / b > 0,
    from div_pos epos bpos,

  cases ct (ε / b) pos with N' h',
  let mN := max N N',
  use mN,
  intros n nge,

  have : |s n * t n - 0| = |s n * t n|,
    by congr; apply sub_zero,
  rw this,

  have ht : |t n - 0| = |t n|,
    by congr; apply sub_zero,

  rw abs_mul,
  have : ε = b * (ε / b),
    calc
      ε = ε * 1 : (mul_one ε).symm 
      ... = ε * (b / b) : by rw div_self (ne_of_gt bpos) 
      ... = b * (ε / b) : by ring,
  rw this,

  apply mul_lt_mul',
  
  show |s n| ≤ b,
    apply le_of_lt,
    apply h n,
    from le_trans (le_max_left N N') nge,

  show |t n| < ε / b,
    rw ht.symm,
    apply h' n,
    from le_trans (le_max_right N N') nge,

  show 0 ≤ |t n|,
    from abs_nonneg (t n),
  
  show 0 < b,
    from bpos,
end


theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
    apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring,
  
  convert converges_to_add h₁ (converges_to_mul_const b cs),
  ext, ring,
  ring,
end


theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
begin
  by_contra abne,
  have : |a - b| > 0,
    apply abs_pos.mpr,
    intro h',
    apply abne,
    linarith,
    exact has_add.to_covariant_class_left ℝ,

  let ε := |a - b| / 2,
  have epos : ε > 0,
    change |a - b| / 2 > 0,
    linarith,

  cases sa ε epos with Na hNa,
  cases sb ε epos with Nb hNb,

  let N := max Na Nb,
  have ha : | 2 * (s N - a)| < |a - b|,
    have : |s N - a| < |a - b| / 2,
      apply hNa N,
      apply le_max_left,
    have : |2| * |s N - a| < |2| * (|a - b| / 2),
      apply mul_lt_mul',
      apply le_refl,
      from this,
      apply abs_nonneg,
      norm_num,
    rw abs_mul,
    have : |2| * (|a - b| / 2) = |a - b|,
      rw mul_div,
      rw mul_comm,
      rw ←mul_div,
      norm_num,
    linarith,
      
  have hb : | 2 * (s N - b)| < |a - b|,
    have : |s N - b| < |a - b| / 2,
      apply hNb N,
      apply le_max_right,
    have : |2| * |s N - b| < |2| * (|a - b| / 2),
      apply mul_lt_mul',
      apply le_refl,
      from this,
      apply abs_nonneg,
      norm_num,
    rw abs_mul,
    have : |2| * (|a - b| / 2) = |a - b|,
      rw mul_div,
      rw mul_comm,
      rw ←mul_div,
      norm_num,
    linarith,

  have ha : |s N - a| < |a - b| / 2,
      apply hNa N,
      apply le_max_left,

  have hb : |s N - b| < |a - b| / 2,
      apply hNb N,
      apply le_max_right, 

  have ab : |a - b| = |a - b|/2 + |a - b|/2,
      norm_num,

  have : |a - b| = | -(s N - a) + (s N - b)|,
    congr,
    linarith,

  have : |a - b| < |a - b|,
    apply lt_of_le_of_lt,
    show |a - b| ≤ | -(s N - a) + (s N - b)|,
    rw this,
    show | -(s N - a) + (s N - b)| < |a - b|,
    apply lt_of_le_of_lt,
    apply abs_add,
    rw ab,
    apply add_lt_add,
      rw abs_neg,
      from ha,
      from hb,
    
  from lt_irrefl _ this,
end


variables {α : Type*} [linear_order α]

def converges_to' (s : α → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε 