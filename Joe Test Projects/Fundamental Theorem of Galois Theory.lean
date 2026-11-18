import Mathlib.FieldTheory.Galois.Basic

/-!
# Fundamental Theorem of Galois Theory

The goal of this file is to formalise the Fundamental Theorem of Galois Theory.
This is a practice project -- in the actual formalisation, we will import the
Fundamental Theorem of Galois Theory from Mathlib.
-/

-- Write p(x) for polynomial evaluation, with no space before the parenthesis.
local macro:max p:term:max noWs "(" x:term ")" : term =>
  `(Polynomial.eval $x $p)

-- We write Fix(H) for the fixed field of H, and Aut(E) for Aut_E(L)
local notation "Fix(" H ")" => IntermediateField.fixedField H
local notation "Aut(" E ")" => IntermediateField.fixingSubgroup E

-- Throughout, L/K is a field extension, and E is an intermediate field
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L)

/-
Given a type α and a predicate p : α → Prop, the expression {x : α // p x} is
itself a type, known as a subtype of α. The elements of the subtype are of the
form ⟨x,hx⟩, where x:α and hx : px is a proof that px is satisfied
-/

/-
In Lean, IntermediateField K L is a record type whose elements consist of
multiple components, which in this context are a subset of L, a proof that it
contains 0, a proof that it contains 1, a proof of closure under addition, a
proof of closure under multiplication, a proof of closure under inversion, and a
proof that it contains the image of K
-/

/-
When we write x : E, note that E is not a type; rather, it is an element of
IntermediateField K L. Lean thus inserts a coercion to the associated subtype
{x : L // x ∈ E.carrier}. This subtype is itself a record type: its elements
contain the two components described above
-/

-- Proof that if E is an intermediate field of L/K, and H is a subgroup of
-- Gal(L/K), then E ≤ Fix(H) if and only if H ≤ Aut(E)
theorem joe_galois_connection (H : Subgroup (Gal(L/K))) :
    E ≤ Fix(H) ↔ H ≤ Aut(E) := by
  constructor
  intro fieldinclusion
  intro σ inH
  intro e
  have h : (e : L) ∈ Fix(H) := by
    exact fieldinclusion e.property
  rw [IntermediateField.mem_fixedField_iff H (e : L)] at h
  exact h σ inH
  intro groupinclusion
  intro e inE
  intro σ
  have h' : (σ : Gal(L/K)) ∈ Aut(E) := by
    exact groupinclusion σ.property
  rw [IntermediateField.mem_fixingSubgroup_iff E (σ : Gal(L/K))] at h'
  exact h' e inE

-- Proof that Aut reverses inclusions
theorem joe_fixingSubgroup_le (F : IntermediateField K L) (hEF : E ≤ F) :
    Aut(F) ≤ Aut(E) := by
  intro σ h e
  have einF : (e : L) ∈ F := by
    exact hEF e.property
  rw [IntermediateField.mem_fixingSubgroup_iff F (σ : Gal(L/K))] at h
  exact h e einF

-- Proof that taking fixed fields reverses inclusions
theorem joe_fixedField_le (H₁ H₂ : Subgroup (Gal(L/K))) (hH : H₁ ≤ H₂) :
    Fix(H₂) ≤ Fix(H₁) := by
  intro x h σ
  have σinH2 : (σ : Gal(L/K)) ∈ H₂ := by
    exact hH σ.property
  rw [IntermediateField.mem_fixedField_iff H₂ (x : L)] at h
  exact h σ σinH2

-- In what follows, recall that E ≤ Fix(H) iff H ≤ Aut(E)

-- Proof that H ≤ Aut(Fix(H))
theorem joe_aut_of_fix (H : Subgroup (Gal(L/K))) :
    H ≤ Aut(Fix(H)) := by
  have trivial_galois : Fix(H) ≤ Fix(H) ↔ H ≤ Aut(Fix(H)) := by
    exact joe_galois_connection Fix(H) H
  exact trivial_galois.mp le_rfl

-- Proof that E ≤ Fix(Aut(E))
theorem joe_fix_of_aut : E ≤ Fix(Aut(E)) := by
  have trivial_galois : E ≤ Fix(Aut(E)) ↔ Aut(E) ≤ Aut(E) := by
    exact joe_galois_connection E Aut(E)
  exact trivial_galois.mpr le_rfl

-- Proof that Aut(Fix(Aut(E))))=Aut(E)
theorem joe_fixingSubgroup_triple : Aut(Fix(Aut(E))) = Aut(E) := by
  have inclusion : Aut(Fix(Aut(E)))≤Aut(E) := by
    have h  := joe_fix_of_aut E
    have h' := joe_fixingSubgroup_le E Fix(Aut(E))
    exact h' h
  have reverse : Aut(E)≤Aut(Fix(Aut(E))) := by
    exact joe_aut_of_fix Aut(E)
  exact le_antisymm inclusion reverse

-- Proof that Fix(Aut(Fix(H))))=Fix(H)
theorem joe_fixedField_triple (H : Subgroup (L ≃ₐ[K] L)) :
    Fix(Aut(Fix(H))) = Fix(H) := by
  have inclusion : Fix(Aut(Fix(H))) ≤ Fix(H) := by
    have h  := joe_aut_of_fix H
    have h' := joe_fixedField_le H Aut(Fix(H))
    exact h' h
  have reverse : Fix(H) ≤ Fix(Aut(Fix(H))) := by
    exact joe_fix_of_aut Fix(H)
  exact le_antisymm inclusion reverse

-- The natural ring homomorphism R -> R[t], sending r to the constant polynomial r.
noncomputable def joePolynomialC (R : Type*) [CommRing R] :
    R →+* Polynomial R := Polynomial.C

-- Definition of the monoid homomorphism End_{Ring}(R) -> End_{Ring}(R[t])
noncomputable def joePolynomialEndMap (R : Type*) [CommRing R] :
    (R →+* R) →* (Polynomial R →+* Polynomial R) where
  toFun := Polynomial.mapRingHom
  map_one' := Polynomial.mapRingHom_id
  map_mul' f g := (Polynomial.mapRingHom_comp f g).symm

-- The group homomorphism Aut_K(L) -> Aut_K(L[t]), acting on coefficients and fixing t.
noncomputable def joePolynomialAutMap
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (L ≃ₐ[K] L) →* (Polynomial L ≃ₐ[K] Polynomial L) where
  toFun := Polynomial.mapAlgEquiv
  map_one' := Polynomial.mapAlgEquiv_id
  map_mul' σ τ := (Polynomial.mapAlgEquiv_comp L τ σ).symm

-- Its underlying ring homomorphism agrees with joePolynomialEndMap.
@[simp]
theorem joePolynomialAutMap_toRingHom (σ : L ≃ₐ[K] L) :
    (joePolynomialAutMap K L σ).toRingHom =
      joePolynomialEndMap L σ.toRingHom := rfl

@[simp]
theorem joePolynomialAutMap_apply (σ : L ≃ₐ[K] L) (p : Polynomial L) :
    joePolynomialAutMap K L σ p = p.map σ.toRingHom := rfl

open scoped BigOperators

-- Given a subgroup H of Aut_K(L), we define joeOrbitPolynomial as the
-- polynomial in L[x] which is the product of the terms x-σ(x), where σ ranges
-- over H
noncomputable def joeOrbitPolynomial
    (H : Subgroup (Gal(L/K))) [Fintype H] (a : L) : Polynomial L :=
  ∏ σ : H, (Polynomial.X - Polynomial.C ((σ : Gal(L/K)) a))

theorem joe_orbitPolynomial_eval_eq_zero_iff
    (H : Subgroup (Gal(L/K))) [Fintype H] (a x : L) :
    (joeOrbitPolynomial H a)(x) = 0 ↔ ∃ σ : H, x = (σ : Gal(L/K)) a := by
  have h : (joeOrbitPolynomial H a)(x) = 0 ↔ ∃ σ : H, x-(σ : Gal(L/K)) a = 0 := by
    unfold joeOrbitPolynomial
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  rw [h]
  simp [sub_eq_zero]

theorem joe_orbitPolynomial_map
    (H : Subgroup (Gal(L/K))) [Fintype H] (a : L) (ρ : H) :
    (joeOrbitPolynomial H a).map (ρ : Gal(L/K)).toRingHom =
      joeOrbitPolynomial H a := by
  sorry
