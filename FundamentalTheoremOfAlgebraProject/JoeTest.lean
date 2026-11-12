import Mathlib

/-!
# JoeTest

A few basic Lean examples.
-/

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

theorem also_stupid : (a+b)*(a-b)=a^2-b^2 := by
  sorry

end
