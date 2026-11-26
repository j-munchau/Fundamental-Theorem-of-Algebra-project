import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField

/-!
# GeneralTheorem

Here, we state the fundamental theorem of algebra in the following general form.
Suppose R is a real closed field, and C is an extension of R for which there is
an element i∈C such that C=R(i) and i^2=-1. Then, C is an algebraic closure of
R.

Once we have established Step~4, there are various ways to conclude that C is
algebraically closed. Here is one argument. It is easy to see that C is a
splitting field of the polynomial $x^2+1$ over $R$. We can use this to show that
every nonzero $f\in R[x]$ splits over $C$: let $M$ be a splitting field of $f$
over $C$. Then, $M$ is a splitting field of $(x^2+1)f$ over $R$. The extension
$R\subseteq M$ is finite Galois and contains $C$, so $M=C$. Hence $f$ splits
over $C$. The following theorem now completes the proof.
\begin{theorem}
Suppose $F\subseteq K$ is an algebraic extension and every polynomial over $F$
splits over $K$. Then, $K$ is an algebraic closure of $F$.
\end{theorem}
-/

open scoped Polynomial IntermediateField

variable {R C L : Type*}
  [Field R] [Field C] [Field L]
  [Algebra R C] [Algebra C L] [Algebra R L]
  [IsScalarTower R C L]
variable {i : C}

local notation "φ" => algebraMap R C
local notation "ψ" => algebraMap C L
local notation "H" => L ≃ₐ[C] L

lemma splitting_field [OurRealClosedField R] (sq : i^2=-1)
(gen : R⟮i⟯ = ⊤) : Polynomial.IsSplittingField R C (Polynomial.X ^ 2 + 1 : R[X]) := by
  rw [isSplittingField_iff_intermediateField]
  sorry

lemma splitting [OurRealClosedField R] (sq : i^2=-1)
(gen : R⟮i⟯ = ⊤) (f : R[X]) : (f.map φ).Splits := by
  by_cases hf : f = 0
  · rw [hf, Polynomial.map_zero]
    exact Polynomial.Splits.zero
  let M := (f.map φ).SplittingField
  have hM :
      Polynomial.IsSplittingField R M ((Polynomial.X ^ 2 + 1) * f : R[X]) := by
    sorry
  sorry

theorem general [OurRealClosedField R] (sq : i ^ 2 = -1)
(gen : R⟮i⟯ = ⊤) : IsAlgClosure R C := by
  have : Algebra.IsIntegral R C := sorry
  exact IsAlgClosure.of_splits fun p _ _ => splitting sq gen p
