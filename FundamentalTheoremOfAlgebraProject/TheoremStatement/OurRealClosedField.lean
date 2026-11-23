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

class OurRealClosedField (R : Type*) [Field R] : Prop where
  oddDegreeRoot : ∀ p : R[X], Odd p.natDegree -> ∃ a : R, p.IsRoot a
  nonNegSquare : ∃ (_ : LinearOrder R),
  IsStrictOrderedRing R ∧ ∀ x : R, 0 ≤ x -> IsSquare x

-- The reals are an instance of our definition of a real closed field
instance : OurRealClosedField ℝ where
  oddDegreeRoot _ hp := IsRealClosed.exists_isRoot_of_odd_natDegree hp
  nonNegSquare := by
    use inferInstance
    constructor
    · infer_instance
    · intro x hx
      exact ⟨√x, (Real.mul_self_sqrt hx).symm⟩
