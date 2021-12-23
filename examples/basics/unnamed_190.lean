import data.real.basic

-- BEGIN
example (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
  rw mul_assoc a,
  rw h,
  rw ← mul_assoc a,
end

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw hyp,
  rw hyp',
  rw mul_comm,
  rw sub_self (a * b),
end
-- END