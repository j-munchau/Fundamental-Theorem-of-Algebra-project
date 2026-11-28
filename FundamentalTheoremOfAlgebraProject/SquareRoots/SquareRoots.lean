import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField
import Mathlib.Algebra.Group.Units.Defs
import FundamentalTheoremOfAlgebraProject.ElementaryResults.ElementaryResults

open Polynomial
open scoped Polynomial
open scoped IntermediateField

variable {R C : Type*} [Field R] [Field C] [Algebra R C]

variable {i : C}

lemma nonneg_square_root [LinearOrder R] [IsStrictOrderedRing R]
      (hs : ∀ {x : R}, 0 ≤ x -> IsSquare x) {x : R} (h: 0 ≤ x) : ∃ r :
      R, 0 ≤ r ∧ x = r ^ 2 := by
  obtain ⟨r, hr⟩ := hs h
  refine ⟨|r|, abs_nonneg r, ?_⟩
  rw [sq_abs, pow_two]
  exact hr

theorem complex_isSquare [OurRealClosedField R] (hsq : i ^ 2 = -1) (gen : R⟮i⟯ = ⊤) (z : C) :
        IsSquare z := by
  obtain ⟨_, _, h⟩ := OurRealClosedField.nonNegSquare (R := R)
  obtain ⟨a, b, hab⟩ := complexRepresentation hsq gen z
  obtain ⟨r, hr⟩ := nonneg_square_root (h) (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hasqrsq := le_of_le_of_eq
                  (le_add_of_nonneg_right (a := a ^ 2) (b := b ^ 2) (sq_nonneg b)) hr.2
  have harabs := abs_le_of_sq_le_sq' hasqrsq hr.1
  have hrpa := div_nonneg (neg_le_iff_add_nonneg.mp harabs.1) zero_le_two
  rw [add_comm a r] at hrpa
  have hrma := div_nonneg (sub_nonneg_of_le harabs.2) zero_le_two
  obtain ⟨x, hx⟩ := h hrpa
  obtain ⟨y, hy⟩ := h hrma
  have hxsqmysq : x ^ 2 - y ^2 = a := by
    rw [sq x, sq y, ← hx, ← hy]
    ring
  have h4xsqysq : 4 * x ^ 2 * y ^ 2 = b ^2 := by
    calc
      4 * x ^ 2 * y ^ 2 = r ^ 2 - a ^ 2 := by
        rw [sq x, sq y, ← hx, ← hy]
        ring
      _ = b ^ 2 := (eq_sub_of_add_eq' hr.2).symm
  have h2xyb : (2 * x * y - b) * (2 * x * y + b) = 0 := by
    ring_nf
    rw [← mul_rotate, h4xsqysq, sub_self (b ^ 2)]
  rcases mul_eq_zero.mp h2xyb with ha | hb
  · refine ⟨(algebraMap R C x + algebraMap R C y * i), ?_⟩
    ring_nf
    simp only [← map_mul, ← map_pow, hsq, mul_neg_one, ← map_neg, add_assoc, ← map_add,
              ← sub_eq_add_neg, mul_comm (_ * i) 2, ← mul_assoc]
    have h2 : (2 : C) = algebraMap R C 2 := (map_ofNat (algebraMap R C) 2).symm
    rw [h2, ← map_mul, ← mul_assoc 2 x y]
    have ha1 : 2 * x * y = b := sub_eq_zero.mp ha
    rw [ha1, hxsqmysq, add_comm, ← mul_one (algebraMap R C a), ← Algebra.smul_def,
        ← Algebra.smul_def]
    exact hab
  · refine ⟨(algebraMap R C x - algebraMap R C y * i),?_⟩
    ring_nf
    simp only [← map_mul, ← map_pow, hsq, mul_neg_one, ← map_neg, add_assoc, ← map_add,
              ← sub_eq_add_neg, mul_comm (_ * i) 2, ← mul_assoc]
    rw [← neg_mul, ← neg_mul]
    have hneg2 : (-2 : C) = algebraMap R C (-2) := by simp only [map_neg, map_ofNat]
    rw [hneg2, ← map_mul, ← mul_assoc (-2) x y]
    have hb1 : - 2 * x * y = b := by linarith [hb]
    rw [hb1, hxsqmysq, add_comm, ← mul_one (algebraMap R C a), ← Algebra.smul_def,
        ← Algebra.smul_def]
    exact hab
