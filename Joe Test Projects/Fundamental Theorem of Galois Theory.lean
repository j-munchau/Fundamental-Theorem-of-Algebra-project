import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Fundamental Theorem of Galois Theory

The goal of this file is to formalise the Fundamental Theorem of Galois Theory.
This is a practice project -- in the actual formalisation, we will import the
Fundamental Theorem of Galois Theory from
Mathlib.
-/

-- Throughout, L/K is a field extension, and E is an intermediate field
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L)

-- E is closed under multiplication
example (x y : L) (hx : x ∈ E) (hy : y ∈ E) : ∃ z : E, (z : L) = x * y := by
  have annoying : x*y∈ E := by exact E.mul_mem hx hy
  use ⟨x*y,annoying⟩

example (z : E) : ∃ x : L, x ∈ E ∧ x = (z : L) := by
  use z
  constructor
  exact z.property
  rfl

-- By definition, E≤F means ∀ {x : L}, x ∈ E → x ∈ F
example (F G : IntermediateField K L)
    (hEF : E ≤ F) (hFG : F ≤ G) : E ≤ G := by
  intro x he
  have hf : x ∈ F := by
    exact hEF he
  exact hFG hf




/-
Given a type α and a predicate p : α → Prop, the expression {x : α // p x} is
itself a type, known as a subtype of α. The elements of the subtype are of the
form ⟨x,hx⟩, where x:α and hx : px is a proof that px is satisfied
-/

/-
In Lean, IntermediateField K L is a record type, a type whose elements consist of multiple
components, which in this context are a subset of L, a proof that it
contains 0, a proof that it contains 1, a proof of closure under addition, a
proof of closure under multiplication, a proof of closure under inversion, and a
proof that it contains the image of K
-/

/-
When we write x:E, note that E is not a type; rather, it is an element of
IntermediateField K L. Lean thus inserts a coercion to the associate subtype
{x:L // x∈E.carrier}. This subtype is itself a record type: its elements contains the two
components described above
-/
