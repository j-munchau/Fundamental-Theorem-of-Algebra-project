import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

open Polynomial
open scoped Polynomial

noncomputable def polyI (R : Type*) [Field R] : R[X] :=
  X ^ 2 + 1

variable {R : Type*} [Field R]

lemma polyI_monic : (polyI R).Monic := by
  have h : (2 : ℕ) ≠ 0 := by decide
  exact monic_X_pow_add_C (1 : R) (n := 2) h

lemma polyI_nonzero : polyI R ≠ 0 := by
  exact polyI_monic.ne_zero

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

variable {C : Type*} [Field C] [Algebra R C]

variable {i : C}

lemma i_isRoot_polyI (sq : i ^ 2 = -1) : aeval i (polyI R) = 0 := by
   unfold polyI
   simp only [map_add, map_pow, aeval_X, map_one]
   rw [sq, neg_add_cancel]

lemma i_isIntegral (sq : i ^ 2 = -1) : IsIntegral R i := by
  use polyI R
  constructor
  · exact polyI_monic
  · rw [← Polynomial.aeval_def]
    exact i_isRoot_polyI sq

lemma minpoly_i [OurRealClosedField R] (sq : i ^ 2 = -1) : minpoly R i = polyI R:= by
  exact ((minpoly.eq_iff_aeval_eq_zero polyI_irreducible polyI_monic).mpr (i_isRoot_polyI sq)).symm

lemma complex_extension_finrank [OurRealClosedField R] (sq : i ^ 2 = -1) (gen : R⟮i⟯ = ⊤)
    : Module.finrank R C = 2 := by
  have h := IntermediateField.adjoin.finrank (i_isIntegral (R := R) sq)
  rw [gen, IntermediateField.finrank_top', minpoly_i sq, polyI_natDegree] at h
  exact h

lemma complex_extension_finiteDimensional [OurRealClosedField R] (sq : i ^ 2 = -1) (gen : R⟮i⟯ = ⊤)
    : FiniteDimensional R C := by
      sorry

noncomputable def complexBasis [OurRealClosedField R] (sq : i ^ 2 = -1)
    (gen : R⟮i⟯ = ⊤) : Module.Basis (Fin 2) R C := by
  have e := IntermediateField.adjoinRootEquivAdjoin R (i_isIntegral sq)
  rw [minpoly_i sq, gen] at e
  have b : Module.Basis (Fin 2) R (AdjoinRoot (polyI R)) := by simpa only [polyI_natDegree] using
    (AdjoinRoot.powerBasisAux polyI_nonzero)
  exact b.map (e.trans IntermediateField.topEquiv).toLinearEquiv
