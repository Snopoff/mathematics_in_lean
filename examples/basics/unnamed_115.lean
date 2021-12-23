import data.real.basic

-- BEGIN
example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_comm a c,
  rw mul_assoc,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ← mul_assoc,
  rw mul_comm a b,
  rw mul_assoc,
end
-- END