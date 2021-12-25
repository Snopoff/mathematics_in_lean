import data.real.basic

variables a b c d : ℝ

-- BEGIN
example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
begin
  rw add_mul,
  rw mul_sub,
  rw mul_sub,
  rw add_sub,
  rw mul_comm b a,
  rw add_comm,
  rw add_sub,
  rw add_comm,
  rw ← add_sub,
  rw ← mul_sub,
  simp,
  rw pow_two a,
  rw pow_two b,

end

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
-- END