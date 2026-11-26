import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

/-!
# OddDegreeExtensions

We prove the following theorem. Suppose R is a real closed field, and K/R is a
finite extension of odd degree. Then K has degree 1 over R. We write φ for the
embedding R->K.
-/

variable {R K : Type*} [Field R] [Field K] [Algebra R K]
local notation "φ" => algebraMap R K

open scoped IntermediateField

theorem odd_degree_extensions [OurRealClosedField R] [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) : Module.finrank R K = 1 := by
  apply Module.finrank_of_bijective_algebraMap
  constructor
  · exact (φ).injective
  · intro α
    have divides : Module.finrank R R⟮α⟯ ∣ Module.finrank R K :=
      Dvd.intro _ (Module.finrank_mul_finrank R R⟮α⟯ K)
    have odd_degree : Odd (Module.finrank R R⟮α⟯) :=
      hodd.of_dvd_nat divides
    have hα : IsIntegral R α := Algebra.IsIntegral.isIntegral α
    have odd_minpoly_degree : Odd (minpoly R α).natDegree := by
      rw [← IntermediateField.adjoin.finrank hα]
      exact odd_degree
    have minpoly_root : ∃ c : R, (minpoly R α).IsRoot c :=
      OurRealClosedField.oddDegreeRoot odd_minpoly_degree
    obtain ⟨c, hc⟩ := minpoly_root
    exact ⟨c, minpoly.root hα hc⟩
