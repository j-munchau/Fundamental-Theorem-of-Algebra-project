import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField


/-!
# TheGaloisExtensionArgument

We prove the following theorem. Suppose R is a real closed field, and C⊇R is an
extension for which there is an element i∈C such that i^2=-1 and C=R(i). If
R⊆C⊆L is a tower of extensions such that R⊆L is finite Galois, then C=L.

Notation: we write φ:R->C for the embedding of R into C, and ψ:C->L for the
embedding of C into L.
-/

variable (R C L : Type*)
  [Field R] [Field C] [Field L]
  [Algebra R C] [Algebra C L] [Algebra R L]
  [IsScalarTower R C L]
local notation "φ" => algebraMap R C
local notation "ψ" => algebraMap C L
