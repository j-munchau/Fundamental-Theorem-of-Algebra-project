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

#check E.add_mem
#check E.mul_mem

-- E is closed under multiplication
example (x y : L) (hx : x ∈ E) (hy : y ∈ E) :
    ∃ z : E, (z : L) = x * y := by
  have annoying : x*y∈ E := by exact E.mul_mem hx hy
  use ⟨x*y,annoying⟩

/-
Given a type α and a predicate p : α → Prop, the expression {x : α // p x} is
itself a type, known as a subtype of α. The elements of the subtype are of the
form ⟨x,hx⟩, where x:α and hx : px
-/
