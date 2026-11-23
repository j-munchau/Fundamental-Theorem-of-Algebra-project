import FundamentalTheoremOfAlgebraProject.Imports
import FundamentalTheoremOfAlgebraProject.TheoremStatement.OurRealClosedField
import FundamentalTheoremOfAlgebraProject.TheSylowArgument.TheSylowArgument

/-!
# TheGaloisExtensionArgument

We prove the following theorem. Suppose R is a real closed field, and C⊇R is an
extension for which there is an element i∈C such that i^2=-1 and C=R(i). If
R⊆C⊆L is a tower of extensions such that R⊆L is finite Galois, then C=L.

Notation: we write φ:R->C for the embedding of R into C, and ψ:C->L for the
embedding of C into L. The automorphism group of L over C is denoted by H. Our
task is to show that ψ is bijective.
-/

variable (R C L : Type*)
  [Field R] [Field C] [Field L]
  [Algebra R C] [Algebra C L] [Algebra R L]
  [IsScalarTower R C L]
variable (i : C)
local notation "φ" => algebraMap R C
local notation "ψ" => algebraMap C L
local notation "H" => L ≃ₐ[C] L

open scoped IntermediateField

lemma finite_galois [FiniteDimensional R L] [IsGalois R L] :
    FiniteDimensional C L ∧ IsGalois C L :=
  ⟨FiniteDimensional.right R C L, IsGalois.tower_top_of_isGalois R C L⟩

lemma deg_pow_two [OurRealClosedField R]
    [FiniteDimensional R L] [IsGalois R L] :
    ∃m : ℕ, Module.finrank C L = 2^m := by
  have div : Module.finrank C L ∣ Module.finrank R L :=
    Module.finrank_dvd_finrank_left R C L
  have pow : ∃n:ℕ, Module.finrank R L = 2^n :=
    sylow_argument
  obtain ⟨n, hn⟩ := pow
  rw [hn] at div
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp div
  exact ⟨m, hm⟩

lemma no_quadratic_extension [OurRealClosedField R] (sq : i^2=-1)
    (gen : R⟮i⟯ = ⊤) [FiniteDimensional R L] [IsGalois R L] :
    ∀ E : IntermediateField C L , Module.finrank C E ≠ 2 := by
  sorry

lemma group_lemma (G : Type*) [Group G] [Finite G] (p : ℕ) (hp : Nat.Prime p)
    (s : ℕ) (hG : Nat.card G = p^s) (t : ℕ) (ht : t ≤ s) :
    ∃ K : Subgroup G, Nat.card K = p^t := by
  have : Fact p.Prime := ⟨hp⟩
  exact Sylow.exists_subgroup_card_pow_prime p (hG ▸ pow_dvd_pow p ht)

lemma trivial_degree [OurRealClosedField R] (sq : i^2=-1)
    (gen : R⟮i⟯ = ⊤) [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank C L = 1 := by
  have pow_two : ∃m : ℕ, Module.finrank C L = 2^m :=
    deg_pow_two R C L
  obtain ⟨m,hm⟩ := pow_two
  have galois : IsGalois C L := IsGalois.tower_top_of_isGalois R C L
  have findim : FiniteDimensional C L := FiniteDimensional.right R C L
  have order : Nat.card H = 2^m := by
    rw [IsGalois.card_aut_eq_finrank, hm]
  have h0 : m=0 := by
    by_contra h
    have sub : ∃K : Subgroup H, Nat.card  K = 2^(m-1) :=
      group_lemma H 2 (Nat.prime_two) m order (m-1) (Nat.sub_le m 1)
    obtain ⟨K,hK⟩ := sub
    let F : IntermediateField C L := IntermediateField.fixedField K
    have deg : Module.finrank F L = 2^(m-1) := by
      calc
        Module.finrank F L = Nat.card K :=
        IntermediateField.finrank_fixedField_eq_card K
        _ = 2^(m-1) := hK
    have deg_two : Module.finrank C F = 2 := by
      calc
        Module.finrank C F = (Module.finrank C L)/(Module.finrank F L) :=
        by rw [← Module.finrank_mul_finrank C F L, Nat.mul_div_cancel _ Module.finrank_pos]
        _ = (2^m)/(2^(m-1)) := by rw [hm, deg]
        _ = 2 := by rw [Nat.pow_div (Nat.sub_le m 1) two_pos,
        Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr h), pow_one]
    exact no_quadratic_extension R C L i sq gen F deg_two
  rw [hm, h0, pow_zero]

theorem galois_extension [OurRealClosedField R] (sq : i^2 = -1)
    (gen : R⟮i⟯ = ⊤) [FiniteDimensional R L] [IsGalois R L] :
    Function.Bijective ψ := by
    exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
        (trivial_degree R C L i sq gen)
