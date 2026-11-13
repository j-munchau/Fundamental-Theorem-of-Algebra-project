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

example (P : Prop) (a b : ℝ)
    (h : (a + 1 = b + 1) → P) : a = b → P := by
      intro equality
      apply h
      rw [equality]

example : ∀ a b : ℝ, a = b → a + 1 = b + 1 := by
  intro a b
  intro j
  rw [j]
