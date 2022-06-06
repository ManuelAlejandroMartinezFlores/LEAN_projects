import data.real.basic

example (a b c : ℝ) : (a * b) * c = b * (a * c) := 
begin 
  rw mul_comm a b,
  rw mul_assoc b a c,
end


example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc b c a,
  rw mul_comm c a,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw mul_comm a (b * c),
  rw mul_assoc b c a,
  rw mul_comm c a,
end


example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  rw mul_comm,
  rw mul_assoc,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw mul_comm a,
  rw mul_assoc,
  rw mul_comm c,
end

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
begin
  rw h',
  rw ←mul_assoc,
  rw h,
  rw mul_assoc,
end


example (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
  rw mul_assoc a b c,
  rw h,
  rw ←mul_assoc,
end

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw hyp,
  rw hyp',
  rw mul_comm,
  rw sub_self,
end

variables a b c d e f g : ℝ

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw [add_mul, mul_add, mul_add],
  rw add_assoc (a * a) (a * b) (b * a + b * b),
  rw ←add_assoc (a * b) (b * a) (b * b),
  rw mul_comm b a,
  rw ←two_mul,
  rw add_assoc,
end

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
          by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b :
          by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     :
          by rw [mul_comm b a, ←two_mul]


example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
begin
  rw [mul_add, add_mul, add_mul, ←add_assoc],
  rw [add_assoc, add_assoc, ←add_assoc (b*c)],
  rw [add_comm (b * c)],
  rw [add_assoc, ←add_assoc, ←add_assoc],
end

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc 
  (a + b) * (c + d) 
      = a * c + b * c + a * d + b * d : 
        by rw [mul_add, add_mul, add_mul, ←add_assoc]
  ... = a * c + (b * c + a * d + b * d) :
        by rw [add_assoc, add_assoc, ←add_assoc (b*c)]
  ... = a * c + (a * d + b * c + b * d) :
        by rw [add_comm (b * c)]
  ... = a * c + a * d + b * c + b * d :
        by rw [add_assoc, ←add_assoc, ←add_assoc]


example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
begin
  rw [add_mul, mul_sub, mul_sub],
  rw [add_sub, sub_add, mul_comm a b],
  rw [sub_self, sub_zero, pow_two, pow_two],
end

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a


example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw hyp' at hyp,
  rw [mul_comm] at hyp,
  rw [←two_mul, ←mul_assoc] at hyp,
  assumption
end

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end


