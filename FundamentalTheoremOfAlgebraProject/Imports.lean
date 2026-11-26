import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.IsRealClosed.Real

/-!
# Imports

This file keeps track of which parts of Mathlib have been imported into the
project. Crucially, we ensure that the proof of the fundamental theorem of
algebra already existing in Mathlib is not used.
-/

assert_not_exists Complex.isAlgClosed Complex.exists_root
