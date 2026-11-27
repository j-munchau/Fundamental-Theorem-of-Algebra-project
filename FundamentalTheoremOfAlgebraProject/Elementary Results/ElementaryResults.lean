import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

open Polynomial
open scoped Polynomial

/-!
The goal of this file is to prove some basic facts about field extensions C/R where R is a real
closed field and i ∈ C is an element such that C = R⟮i⟯ and i ^ 2 = -1. For example, we will show
that [C : R] = 2 and that 1 , i is an R-basis for C.
-/

-- We give a definition to the candidate minimal polynomial for i
noncomputable def polyI (R : Type*) [Field R] : R[X] :=
  X ^ 2 + 1

variable {R : Type*} [Field R]

-- We prove some basic facts about our candidate polynomial
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
  apply FiniteDimensional.of_finrank_pos
  rw [complex_extension_finrank sq gen]
  exact Nat.zero_lt_two

/-!
We now want to show that 1 , i is an R-basis for C. Instead of showing this directly, we will appeal
to the power basis results from mathlib and extract the relevant results from there.
-/

noncomputable def complexPowerBasis [OurRealClosedField R] (sq : i ^ 2 = -1)
                  (gen : R⟮i⟯ = ⊤) : PowerBasis R C :=
  PowerBasis.ofAdjoinSimpleEqTop (i_isIntegral sq) gen

lemma complexPowerBasis_dim [OurRealClosedField R] (sq : i ^ 2 = -1)
      (gen : R⟮i⟯ = ⊤) : (complexPowerBasis sq gen).dim = 2 := by
  simp [complexPowerBasis, minpoly_i sq, polyI_natDegree]


/-!
Since (complexPowerBasis sq gen).basis is indexed by Fin (complexPowerBasis sq gen).dim, and we
know that this dimension is 2, then we can introduce our definition of the complex basis indexed
by Fin 2.
-/
noncomputable def complexBasis [OurRealClosedField R] (sq : i ^ 2 = -1)
                  (gen : R⟮i⟯ = ⊤) : Module.Basis (Fin 2) R C :=
  (complexPowerBasis sq gen).basis.reindex (finCongr (complexPowerBasis_dim sq gen))

-- Now we prove that our reindexed basis still satisfies the normal power basis property
lemma complexBasis_eq_pow [OurRealClosedField R] (sq : i ^ 2 = -1)
      (gen : R⟮i⟯ = ⊤) (j : Fin 2)
      : complexBasis sq gen j = i ^ (j : ℕ) := by
  let P := complexPowerBasis sq gen
  let e := finCongr (complexPowerBasis_dim sq gen)
  change (P.basis.reindex e) j = i ^ (j : ℕ)
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change i ^ (j : ℕ) = i ^ (j : ℕ)
  rfl

lemma complexBasis_zero [OurRealClosedField R] (sq : i ^ 2 = -1)
      (gen : R⟮i⟯ = ⊤) : complexBasis sq gen 0 = 1 := by
  rw [complexBasis_eq_pow]
  simp

lemma complexBasis_one [OurRealClosedField R] (sq : i ^ 2 = -1)
      (gen : R⟮i⟯ = ⊤) : complexBasis sq gen 1 = i := by
  rw [complexBasis_eq_pow]
  simp

local notation "ι" => algebraMap R C

lemma complexRepresentation [OurRealClosedField R] (sq : i ^ 2 = -1)
      (gen : R⟮i⟯ = ⊤) (z : C) : ∃ (a b : R), z = ι a + ι b * i := by
  refine ⟨(complexBasis sq gen).repr z 0, (complexBasis sq gen).repr z 1, ?_⟩
  simpa only [Fin.sum_univ_two, complexBasis_zero sq gen, complexBasis_one sq gen, Algebra.smul_def,
             mul_one] using ((complexBasis sq gen).sum_repr z).symm

lemma complexRepresentation_unique [OurRealClosedField R] (sq : i ^ 2 = -1)
      (gen : R⟮i⟯ = ⊤) (a b c d : R)
      (h : ι a + ι b * i = ι c + ι d * i)
      : a = c ∧ b = d := by
  rw [← mul_one (ι a), ← mul_one (ι c)] at h
  sorry
