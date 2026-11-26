import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

open Polynomial
open scoped Polynomial

noncomputable def polyI (R : Type*) [Field R] : R[X] :=
  X ^ 2 + 1

variable {R : Type*} [Field R]

lemma polyI_monic : (polyI R).Monic := by
  have h : (2 : ℕ) ≠ 0 := by decide
  exact monic_X_pow_add_C (1 : R) (n := 2) h

lemma polyI_natDegree : (polyI R).natDegree = 2 := by
  unfold polyI
  simp

lemma polyI_noRoot [OurRealClosedField R] : ∀ a : R,
      ¬(polyI R).IsRoot a := by
  intro a ha
  simp only [polyI, Polynomial.IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at ha
  apply eq_neg_of_add_eq_zero_left (a := a ^ 2) (b := 1) at ha
  exact square_ne_minus_one a ha

lemma polyI_irreducible [OurRealClosedField R]
      : Irreducible (polyI R) := by
  have hdeg : (polyI R).natDegree ∈ Finset.Icc 1 3 := by
    rw [polyI_natDegree]
    decide
  exact irreducible_of_degree_le_three_of_not_isRoot hdeg (polyI_noRoot)

open scoped IntermediateField

variable {C : Type*} [Field C] [Algebra R C] [OurRealClosedField R]

