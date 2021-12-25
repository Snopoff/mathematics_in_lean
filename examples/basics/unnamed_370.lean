import data.real.basic

variables a b c d : ℝ

-- BEGIN
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc 
  (a + b) * (c + d) 
    = a * (c + d) + b * (c + d) :
      begin
        rw add_mul,
      end
    ... = a * c + a * d + b * c + b * d : by rw [mul_add, mul_add, ← add_assoc]
-- END