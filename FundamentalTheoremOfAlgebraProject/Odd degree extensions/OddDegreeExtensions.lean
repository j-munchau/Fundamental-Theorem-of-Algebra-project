import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

/-!
# OddDegreeExtensions

We prove the following theorem. Suppose R is a real closed field, and K/R is a
finite extension of odd degree. Then R->K is an isomorphism.
-/

-- K/R is a field extension
variable {R K : Type*} [Field R] [Field K] [Algebra R K]

-- Statement of the theorem
theorem odd_degree_extension (rc : ourRealClosedField R) [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) : Function.Bijective (algebraMap R K) := by
  sorry
