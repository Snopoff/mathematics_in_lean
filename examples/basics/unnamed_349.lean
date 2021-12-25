import data.real.basic

variables a b : ℝ

-- BEGIN
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
    begin
      rw mul_add,
      rw add_mul, 
      rw add_mul,
    end
  ... = a * a + (b * a + a * b) + b * b : by rw [← add_assoc, ← add_assoc]
  ... = a * a + 2 * (a * b) + b * b     : by rw [two_mul, mul_comm b a]
-- END