import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

-- BEGIN
theorem add_neg_cancel_right (a b : R) : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg b, add_zero]
-- END

end my_ring