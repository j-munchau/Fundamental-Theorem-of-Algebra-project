import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField
import FundamentalTheoremOfAlgebraProject.«Odd degree extensions».OddDegreeExtensions

/-!
# TheSylowArgument

We prove the following theorem. Suppose R is a real closed field, and L/R is a
finite Galois extension. Then, L has degree a power of 2 over R. (We allow for
the possibility that the degree is 1.)

Notation: we write φ:R->L for the embedding, and G for the automorphism group of
L over R.
-/

variable {R L : Type*} [Field R] [Field L] [Algebra R L]
local notation "φ" => algebraMap R L
local notation "G" => L ≃ₐ[R] L

open scoped IntermediateField

theorem sylow_argument (rc : ourRealClosedField R) [FiniteDimensional R L]
    [IsGalois R L] : ∃ n : ℕ, Module.finrank R L = 2^n := by
  have correct_autos : Nat.card G = Module.finrank R L :=
    IsGalois.card_aut_eq_finrank R L
  have decomp : ∃n m : ℕ, ∃P : Subgroup G,
      Odd m ∧ Nat.card G = 2^n*m  ∧ Nat.card P = 2^n := by
    have nonzero : Nat.card G ≠ 0 := by
      exact (Nat.card_pos (α := G)).ne'
    have nm : ∃ n m : ℕ, Odd m ∧ Nat.card G = 2^n*m := by
      exact Nat.exists_eq_two_pow_mul_odd nonzero
    obtain ⟨n,m,h,h'⟩ := nm
    have div : 2^n ∣ Nat.card G := by
      exact Dvd.intro m (Eq.symm h')
    have hP : ∃ P : Subgroup G, Nat.card P = 2^n := by
      exact Sylow.exists_subgroup_card_pow_prime 2 div
    tauto
  obtain ⟨n, m, P, hm, hcard, hP⟩ := decomp
  let E : IntermediateField R L := IntermediateField.fixedField P
  have fundamental : IntermediateField.fixingSubgroup E = P := by
    exact IntermediateField.fixingSubgroup_fixedField P
  have galois_again : IsGalois E L := by
    infer_instance
  have correct_autos_again : Nat.card P = Module.finrank E L := by
    rw [← fundamental]
    exact (Nat.card_congr (IntermediateField.fixingSubgroupEquiv E).toEquiv).trans
      (IsGalois.card_aut_eq_finrank E L)
  have hm' : m=Module.finrank R E := by
    calc
      m = (2^n * m)/2^n := by simp
      _ = (Module.finrank R L) / (Module.finrank E L) := by
        rw [← hcard, correct_autos, ← hP, correct_autos_again]
      _ = Module.finrank R E := by
        exact Module.finrank_div_finrank_cancel_right_of_nontrivial R E L
  have hm'' : m=1 := by
    rw [hm']
    exact odd_degree_extensions rc (by simpa only [hm'] using hm)
  have hcard' : Nat.card G = 2^n := by
    simpa [hm''] using hcard
  rw [←correct_autos]
  use n
