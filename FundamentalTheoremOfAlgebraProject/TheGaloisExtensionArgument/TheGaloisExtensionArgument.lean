import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

/-!
# TheGaloisExtension

We prove the following theorem. Suppose R is a real closed field, and K/R is a
finite extension of odd degree. Then K has degree 1 over R. We write φ for the
embedding R->K.
-/

variable {R K : Type*} [Field R] [Field K] [Algebra R K]
local notation "φ" => algebraMap R K
