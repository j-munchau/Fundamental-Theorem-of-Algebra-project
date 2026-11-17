import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField
import FundamentalTheoremOfAlgebraProject.«Odd degree extensions».OddDegreeExtensions

/-!
# TheSylowArgument

We prove the following theorem. Suppose R is a real closed field, and L/R is a
finite Galois extension. Then, L has degree a power of 2 over R. (We allow for
the possibility that the degree is 1.)
-/

-- L/R is a field extension, φ:R->L is the embedding, and G is the automorphism
-- group of L over R
variable {R L : Type*} [Field R] [Field L] [Algebra R L]
local notation "φ" => algebraMap R L
local notation "G" => L ≃ₐ[R] L

open scoped IntermediateField

theorem sylow_argument (rc : ourRealClosedField R) [FiniteDimensional R L]
    [IsGalois R L] : ∃ n : ℕ, Module.finrank R L = 2^n := by
  have correct_autos : Nat.card G = Module.finrank R L := by
    sorry
  sorry
