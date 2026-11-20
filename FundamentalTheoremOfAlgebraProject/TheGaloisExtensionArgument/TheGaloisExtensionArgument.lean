import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField
import FundamentalTheoremOfAlgebraProject.TheSylowArgument.TheSylowArgument

/-!
# TheGaloisExtensionArgument

We prove the following theorem. Suppose R is a real closed field, and C⊇R is an
extension for which there is an element i∈C such that i^2=-1 and C=R(i). If
R⊆C⊆L is a tower of extensions such that R⊆L is finite Galois, then C=L.

Notation: we write φ:R->C for the embedding of R into C, and ψ:C->L for the
embedding of C into L. The automorphism group of L over R is denoted by G. Our
task is to show that ψ is surjective.
-/

variable (R C L : Type*)
  [Field R] [Field C] [Field L]
  [Algebra R C] [Algebra C L] [Algebra R L]
  [IsScalarTower R C L]
variable (i : C)
local notation "φ" => algebraMap R C
local notation "ψ" => algebraMap C L
local notation "G" => L ≃ₐ[R] L

open scoped IntermediateField

theorem galois_extension (rc : ourRealClosedField R) (sq : i^2 = -1)
    (gen : R⟮i⟯ = ⊤) [FiniteDimensional R L] [IsGalois R L] :
    Function.Surjective ψ := by
  let H : Subgroup G := IntermediateField.fixingSubgroup (R⟮ψ i⟯)
  have htriv : H = ⊥ := by
    by_contra hH
    have maximal_subgroup : ∃ K : Subgroup H, K.index = 2 := by
      sorry
    obtain ⟨K,hK⟩ := maximal_subgroup
    let K' : Subgroup G := K.map H.subtype
    let F : IntermediateField R L := IntermediateField.fixedField K'
    have hgenF : R⟮ψ i⟯ ≤ F := by
      sorry
    have hC : ∀ c : C, ψ c ∈ F := by
      sorry
    let F' : IntermediateField C L := F.toSubfield.toIntermediateField hC
    have hdegree :
    Module.finrank C L = Module.finrank C F' * Module.finrank F L := by
      exact (Module.finrank_mul_finrank C F' L).symm
    have galois : IsGalois C L := by
      sorry
    
