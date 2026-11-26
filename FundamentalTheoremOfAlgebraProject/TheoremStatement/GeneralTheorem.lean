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

variable (R C L : Type*)
  [Field R] [Field C] [Field L]
  [Algebra R C] [Algebra C L] [Algebra R L]
  [IsScalarTower R C L]
variable {i : C}

local notation "φ" => algebraMap R C
local notation "ψ" => algebraMap C L
local notation "H" => L ≃ₐ[C] L

lemma finite_extension_trivial [OurRealClosedField R] (sq : i^2=-1)
(gen : R⟮i⟯ = ⊤) [FiniteDimensional C L] : Function.Bijective ψ := by
  sorry

theorem general [OurRealClosedField R] (sq : i ^ 2 = -1)
(gen : R⟮i⟯ = ⊤) : IsAlgClosure R C := by
  sorry
