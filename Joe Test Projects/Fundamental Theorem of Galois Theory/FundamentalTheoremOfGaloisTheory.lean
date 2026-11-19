import FundamentalTheoremOfAlgebraProject.Imports

/-!
# FundamentalTheoremOfGaloisTheory

We prove the following weak version of the fundamental theorem of Galois theory.
Suppose L/K is a field extension with automorphism group G. If H is a finite
subgroup of G, then H is the automorphism group of L over L^H.

Notation: Given a polynomial p, we write p(x) for its value at x. We write
φ:K->L for the embedding, and G for Aut_K(L). Given a subgroup H of G, we write
Fix(H) for its fixed field; in the other direction, if E is a subextension of
L/K, we write Aut(E) for Aut_E(L). In this notation, the desired conclusion is H=Aut(Fix(H)).
-/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L)
local notation "φ" => algebraMap K L
local notation "G" => L ≃ₐ[K] L
local macro:max p:term:max noWs "(" x:term ")" : term =>
  `(Polynomial.eval $x $p)
local notation "Fix(" H ")" => IntermediateField.fixedField H
local notation "Aut(" E ")" => IntermediateField.fixingSubgroup E

open scoped IntermediateField
open scoped BigOperators

-- Proof that if E is an intermediate field of L/K, and H is a subgroup of
-- G, then E ≤ Fix(H) if and only if H ≤ Aut(E).
theorem galois_connection (H : Subgroup G) :
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
  have h' : (σ : G) ∈ Aut(E) := by
    exact groupinclusion σ.property
  rw [IntermediateField.mem_fixingSubgroup_iff E (σ : G)] at h'
  exact h' e inE

-- Proof that Aut reverses inclusions.
theorem fixingSubgroup_le (F : IntermediateField K L) (hEF : E ≤ F) :
    Aut(F) ≤ Aut(E) := by
  intro σ h e
  have einF : (e : L) ∈ F := by
    exact hEF e.property
  rw [IntermediateField.mem_fixingSubgroup_iff F (σ : G)] at h
  exact h e einF

-- Proof that taking fixed fields reverses inclusions.
theorem fixedField_le (H₁ H₂ : Subgroup G) (hH : H₁ ≤ H₂) :
    Fix(H₂) ≤ Fix(H₁) := by
  intro x h σ
  have σinH2 : (σ : G) ∈ H₂ := by
    exact hH σ.property
  rw [IntermediateField.mem_fixedField_iff H₂ (x : L)] at h
  exact h σ σinH2

-- In what follows, recall that E ≤ Fix(H) iff H ≤ Aut(E).

-- Proof that H ≤ Aut(Fix(H)).
theorem aut_of_fix (H : Subgroup G) :
    H ≤ Aut(Fix(H)) := by
  have trivial_galois : Fix(H) ≤ Fix(H) ↔ H ≤ Aut(Fix(H)) := by
    exact galois_connection Fix(H) H
  exact trivial_galois.mp le_rfl

-- Proof that E ≤ Fix(Aut(E)).
theorem fix_of_aut : E ≤ Fix(Aut(E)) := by
  have trivial_galois : E ≤ Fix(Aut(E)) ↔ Aut(E) ≤ Aut(E) := by
    exact galois_connection E Aut(E)
  exact trivial_galois.mpr le_rfl

/-
-- Proof that Aut(Fix(Aut(E))) = Aut(E).
theorem fixingSubgroup_triple : Aut(Fix(Aut(E))) = Aut(E) := by
  have inclusion : Aut(Fix(Aut(E))) ≤ Aut(E) := by
    have h := fix_of_aut E
    have h' := fixingSubgroup_le E Fix(Aut(E))
    exact h' h
  have reverse : Aut(E) ≤ Aut(Fix(Aut(E))) := by
    exact aut_of_fix Aut(E)
  exact le_antisymm inclusion reverse

-- Proof that Fix(Aut(Fix(H))) = Fix(H).
theorem fixedField_triple (H : Subgroup G) :
    Fix(Aut(Fix(H))) = Fix(H) := by
  have inclusion : Fix(Aut(Fix(H))) ≤ Fix(H) := by
    have h := aut_of_fix H
    have h' := fixedField_le H Aut(Fix(H))
    exact h' h
  have reverse : Fix(H) ≤ Fix(Aut(Fix(H))) := by
    exact fix_of_aut Fix(H)
  exact le_antisymm inclusion reverse
-/

-- The group homomorphism Aut_K(L) -> Aut_K(L[t]), acting on coefficients and fixing t.
noncomputable def autMap
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (L ≃ₐ[K] L) →* (Polynomial L ≃ₐ[K] Polynomial L) where
  toFun := Polynomial.mapAlgEquiv
  map_one' := Polynomial.mapAlgEquiv_id
  map_mul' σ τ := (Polynomial.mapAlgEquiv_comp L τ σ).symm

-- Given a subgroup H of G, we define orbitPolynomial as the
-- polynomial in L[t] which is the product of the terms t-σ(a), where σ ranges
-- over H
noncomputable def orbitPolynomial
    (H : Subgroup G) [Fintype H] (a : L) : Polynomial L :=
  ∏ σ : H, (Polynomial.X - Polynomial.C ((σ : G) a))

-- The orbitPolynomial vanishes at a point x∈L iff x=σ(a) for some σ∈G
theorem orbitPolynomial_eval_eq_zero_iff
    (H : Subgroup G) [Fintype H] (a x : L) :
    (orbitPolynomial H a)(x) = 0 ↔ ∃ σ : H, x = (σ : G) a := by
  have h : (orbitPolynomial H a)(x) = 0 ↔ ∃ σ : H, x-(σ : G) a = 0 := by
    unfold orbitPolynomial
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  rw [h]
  simp [sub_eq_zero]

/-
theorem orbitPolynomial_map
    (H : Subgroup G) [Fintype H] (a : L) (ρ : H) :
    (orbitPolynomial H a).map (ρ : G).toRingHom =
      orbitPolynomial H a := by
  sorry

noncomputable def orbitPolynomial
    (H : Subgroup G) [Fintype H] (a : L) : Polynomial L :=
  ∏ σ : H, (Polynomial.X - Polynomial.C ((σ : G) a))
-/

-- The equaliser {σ=τ} of two automorphisms σ,τ ∈ G
def equaliser (σ τ : G) : Set L :=
  {x : L | σ x = τ x}

-- The equaliser of two automorphisms σ,τ ∈ G is a subfield of L
lemma equaliser_subfield (σ τ : G) :
    ∃K : Subfield L, (K : Set L) = equaliser σ τ := by
  exact ⟨RingHom.eqLocusField σ.toRingHom τ.toRingHom, rfl⟩

-- Given τ∈G and H≤G, the union of the equalisers {σ=τ}, where σ ranges over H
def subgroupSubset (H : Subgroup G) (τ : G) : Set L :=
  ⋃ σ : H, (equaliser σ τ)

-- If L is written as a finite union of subfields, then one of the subfields is
-- L itself
lemma union_subfields {ι} [Fintype ι] (S : ι → Set L) :
    (∀i:ι, ∃ K : Subfield L, (K : Set L) = S i) ∧ ⋃i:ι, S i = Set.univ
    → (∃i:ι, Set.univ = S i) := by
  intro h
  obtain ⟨hfields, hcover⟩ := h
  choose F hF using hfields
  cases finite_or_infinite L with
  | inl h =>
      let : Finite L := h
      have cyclic : IsCyclic Lˣ := by
         infer_instance
      obtain ⟨x,hx⟩ := cyclic
      have triv : (x:L) ∈ Set.univ := by
        trivial
      have in_union : (x:L) ∈ ⋃i:ι, S i := by
        rw [← hcover] at triv
        exact triv
      have in_Si : ∃i:ι, (x:L) ∈ S i := by
        exact Set.mem_iUnion.mp in_union
      obtain ⟨i,g⟩ := in_Si
      have in_Fi : (x:L) ∈ F i := by
        rw [← hF] at g
        exact g
      let xF : F i := ⟨(x : L), in_Fi⟩
      have nonzero : xF≠0 := by
        refine Subtype.coe_ne_coe.mp ?_
        exact x.ne_zero
      let y : (F i).toSubmonoid.units :=
  ⟨x, in_Fi, by simpa using (F i).inv_mem in_Fi⟩
      have hgen : Subgroup.zpowers x = ⊤ := by
        apply (Subgroup.eq_top_iff' _).mpr
        intro z
        exact Subgroup.mem_zpowers_iff.mpr (hx z)
      have hunits : (F i).toSubmonoid.units = ⊤ := by
        apply top_le_iff.mp
        rw [← hgen]
        exact Subgroup.zpowers_le.mpr y.property
      



  | inr h =>
      let : Infinite L := h
      sorry

-- To prove the main theorem, it suffices to show that for every τ∈Aut(Fix(H)),
-- the field L is the union of the sets {σ=τ}, where σ ranges over H
lemma reduction (H : Subgroup G) [Fintype H] :
    (∀τ:Aut(Fix(H)), Set.univ = subgroupSubset H τ)
    → (Aut(Fix(H)))≤ H := by
  intro h τ hτ
  have union : Set.univ = ⋃σ:H, (equaliser σ τ) := by
    exact h ⟨τ,hτ⟩
  have trivial_union :
      ∃σ:H, Set.univ = equaliser (σ:G) (τ:G) := by
    apply union_subfields
    constructor
    · intro σ
      exact equaliser_subfield (σ:G) (τ:G)
    · exact union.symm
  obtain ⟨σ,eq⟩ := trivial_union
  have sigma_tau : (σ:G)=(τ:G) := by
    ext x
    have hx : x ∈ equaliser (σ : G) (τ : G) := by
      rw [← eq]
      trivial
    exact hx
  rw [← sigma_tau]
  exact σ.property

-- The main theorem
theorem weak_fundamental_theorem (H : Subgroup G) [Finite H] :
    H=Aut(Fix(H)) := by
  let : Fintype H := Fintype.ofFinite H
  ext
  constructor
  · have inclusion : H≤Aut(Fix(H)) := aut_of_fix H
    intro x
    exact inclusion x
  · apply reduction
    intro τ
    sorry
