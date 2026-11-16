import FundamentalTheoremOfAlgebraProject.Imports

/-!
# GeneralTheorem

Here, we state the fundamental theorem of algebra in the following general form.
Suppose R is a real closed field, and C is an extension of R for which there is
an element i∈C such that C=R(i) and i^2=-1. Then, C is an algebraic closure of
R.
-/

-- C/R is a field extension
variable {R C : Type*} [Field R] [Field C] [Algebra R C]
