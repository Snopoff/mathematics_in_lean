import data.real.basic

-- BEGIN
example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  rw mul_comm,
  rw mul_assoc,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ← mul_assoc a,
  rw mul_comm a,
  rw mul_assoc b,
end
-- END