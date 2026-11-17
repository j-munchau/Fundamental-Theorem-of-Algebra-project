import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Imports

This file keeps track of which parts of Mathlib have been imported into the
project. Crucially, we ensure that the proof of the fundamental theorem of
algebra already existing in Mathlib is not used.
-/

assert_not_imported Mathlib.Analysis.Complex.Polynomial.Basic
