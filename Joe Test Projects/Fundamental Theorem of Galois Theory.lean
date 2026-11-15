import Mathlib.FieldTheory.Galois.Basic

/-!
# Fundamental Theorem of Galois Theory

The goal of this file is to formalise the Fundamental Theorem of Galois Theory.
This is a practice project -- in the actual formalisation, we will import the
Fundamental Theorem of Galois Theory from Mathlib.
-/

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
