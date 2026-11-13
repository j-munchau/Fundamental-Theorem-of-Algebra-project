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

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro conjuncts
  constructor
  exact conjuncts.2
  exact conjuncts.1

example (a b : ℝ) (h : a = b) :
    ∃ x : ℝ, x - a = 0 ∧ x - b = 0 := by
      use a
      constructor
      exact sub_self a
      rw [h]
      exact sub_self b

example (a b : ℝ)
    (h : ∃ x : ℝ, x - a = 0 ∧ x - b = 0) :
    ∃ x : ℝ, x - b = 0 := by
  obtain ⟨x, hx⟩ := h
  use x
  exact hx.2

example (P Q R : Prop) (hPQ : P ↔ Q) (hQR : Q ↔ R) :
    P ↔ R := by
  constructor
  intro h
  exact hQR.mp (hPQ.mp h)
  intro h'
  exact hPQ.mpr (hQR.mpr h')

example (a b : ℝ) (h : a = b) (hb : b ≠ 0) : a ≠ 0 := by
  intro ha
  rw [h] at ha
  tauto

example (a b : ℝ) (h : a = b) (hb : b ≠ 0) : a ≠ 0 := by
  intro ha
  rw [h] at ha
  apply hb
  exact ha

example (a b : ℝ) (h : a = b) (hb : b ≠ 0) : a ≠ 0 := by
  intro ha
  apply hb
  rw [← h]
  exact ha

def HasRealSquareRoot (a : ℝ) : Prop :=
  ∃ r : ℝ, r * r = a

example (a : ℝ) (h : HasRealSquareRoot a) :
    ∃ r : ℝ, r * r - a = 0 := by
    unfold HasRealSquareRoot at h
    obtain ⟨r,hr⟩ := h
    use r
    rw [hr]
    exact sub_self a

def HasSquareRootIn (K : Type*) [Field K] (a : K) : Prop :=
  ∃ r : K, r^2 = a

def OddDegreeRootProperty (K : Type*) [Field K] : Prop :=
  ∀ f : Polynomial K, Odd f.natDegree -> ∃ a : K, f.IsRoot a

example (K L : Type*) [Field K] [Field L] [Algebra K L]
    (a : K) (h : HasSquareRootIn K a) :
    HasSquareRootIn L (algebraMap K L a) := by
  unfold HasSquareRootIn at h
  obtain ⟨r,hr⟩ := h
  unfold HasSquareRootIn
  use algebraMap K L r
  have hmap : algebraMap K L (r^2) = algebraMap K L a := by rw [hr]
  have preserve :
    algebraMap K L (r ^ 2) = (algebraMap K L r) ^ 2 := by
    exact map_pow (algebraMap K L) r 2
  rw [← preserve]
  exact hmap
