import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

-- BEGIN
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
  by rw [← add_neg_cancel_left a b, ← add_assoc, add_comm, 
         ← add_assoc, add_comm b a, h, add_comm a c, add_assoc, add_right_neg, add_zero]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
  by rw [← add_neg_cancel_right a b, h, add_assoc, add_right_neg, add_zero]
-- END

end my_ring