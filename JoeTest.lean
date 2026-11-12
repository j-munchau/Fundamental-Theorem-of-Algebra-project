import Mathlib

/-!
# JoeTest

A few basic Lean examples.
-/

example (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
      exact hQR (hPQ hP)

example (a b c : ℝ) (hab : a = b) (hbc : b = c) :
    a + 1 = c + 1 := by
  rw [hab]
  rw [hbc]

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) :
    P → R := by
  intro hP
  exact hQR (hPQ hP)
