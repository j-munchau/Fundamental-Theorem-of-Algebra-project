import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

/-!
# OddDegreeExtensions

We prove the following theorem. Suppose R is a real closed field, and K/R is a
finite extension of odd degree. Then K has degree 1 over R.
-/

-- K/R is a field extension
variable {R K : Type*} [Field R] [Field K] [Algebra R K]
local notation "φ" => algebraMap R K

open scoped IntermediateField

-- Odd degree extensions theorem
theorem odd_degree_extension (rc : ourRealClosedField R) [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) : Module.finrank R K = 1 := by
  have bij : Function.Bijective φ → Module.finrank R K = 1 := by
    exact Module.finrank_of_bijective_algebraMap
  apply bij
  constructor
  · exact (φ).injective
  · intro α
    have degree_mul : (Module.finrank R K) =
        (Module.finrank R R⟮α⟯) * (Module.finrank R⟮α⟯ K) := by
      exact (Module.finrank_mul_finrank R R⟮α⟯ K).symm
    have divides : (Module.finrank R R⟮α⟯) ∣ (Module.finrank R K) := by
      use Module.finrank R⟮α⟯ K
    have odd_degree : Odd (Module.finrank R R⟮α⟯) := by
      exact hodd.of_dvd_nat divides
    have odd_minpoly_degree : Odd (minpoly R α).natDegree := by
      have hα : IsIntegral R α := Algebra.IsIntegral.isIntegral α
      rw [← IntermediateField.adjoin.finrank hα]
      exact odd_degree
    have minpoly_root : ∃ c : R, (minpoly R α).IsRoot c := by
      have rootProperty : oddDegreeRootProperty R := by
        exact rc.left
      unfold oddDegreeRootProperty at rootProperty
      apply rootProperty
      exact odd_minpoly_degree
    obtain ⟨c, hc⟩ := minpoly_root
    have hα : IsIntegral R α := Algebra.IsIntegral.isIntegral α
    exact ⟨c, minpoly.root hα hc⟩
