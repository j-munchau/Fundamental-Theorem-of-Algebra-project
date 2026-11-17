import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

/-!
# GeneralTheorem

Here, we state the fundamental theorem of algebra in the following general form.
Suppose R is a real closed field, and C is an extension of R for which there is
an element i∈C such that C=R(i) and i^2=-1. Then, C is an algebraic closure of
R.
-/

open scoped IntermediateField

variable {R C : Type*} [Field R] [Field C] [Algebra R C]
variable (i : C)

theorem general (rc : ourRealClosedField R) (sq : i ^ 2 = -1)
(gen : R⟮i⟯ = ⊤) : IsAlgClosure R C := by
  sorry
