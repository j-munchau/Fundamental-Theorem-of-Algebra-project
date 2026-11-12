import Mathlib

/-!
# JoeTest

A few basic Lean examples.
-/

theorem stupid (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc]

/-!
theorem stupid (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [h]

section

variable (a b : ℝ)

theorem also_stupid : (a+b)*(a-b)=a^2-b^2 :=
  calc
    (a+b)*(a-b)=(a+b)*a-(a+b)*b := by
      rw [mul_sub]
    _ = (a^2+b*a)-(a*b+b^2) := by
      rw [add_mul, add_mul, pow_two, pow_two]
    _ = (a^2+b*a)-(b^2+b*a) := by
      rw [mul_comm a b]
      rw [add_comm (b*a) (b^2)]
    _ = a^2-b^2 := by
      rw [add_sub_add_right_eq_sub]

theorem also_stupid2 : (a+b)*(a-b)=a^2 - b^2 := by
  ring

end

section

variable (R : Type*) [CommRing R]

end
-/
