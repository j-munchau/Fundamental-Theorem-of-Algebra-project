import FundamentalTheoremOfAlgebraProject.Imports

/-!
# OurRealClosedField

The goal of this file is to formalise the definition of real closed field that
we will use in the project. We define a real closed field as a field R which is
similar to the reals in the following sense: (i) every polynomial of odd degree
in R has a root in R, and (ii) There exists a total order <= on R such that R is
an ordered field under this ordering, and moreover, every positive element of R
is a square. MathLib already has a definition of real closed field which is
equivalent to our one, but we intend to mainly use our own definition in the
proof.
-/

open Polynomial

-- Condition (i)
def oddDegreeRootProperty (R : Type*) [Field R] : Prop :=
  ∀ p : R[X], Odd p.natDegree -> ∃ a : R, p.IsRoot a

-- Condition (ii)
def orderingProperty (R : Type*) [Field R] : Prop :=
  ∃ (_ : LinearOrder R), IsStrictOrderedRing R ∧ ∀ x : R, 0 ≤ x -> IsSquare x

-- Our definition of real closed field
def ourRealClosedField (R : Type*) [Field R] : Prop :=
  oddDegreeRootProperty R ∧ orderingProperty R
