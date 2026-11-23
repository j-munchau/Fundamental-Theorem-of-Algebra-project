import Mathlib.FieldTheory.Galois.Basic

example (K L : Type*) [Field K] [Field L] [Algebra K L]
    (B : Module.Basis (Fin 2) K L) (c : Fin 2 → K) :
    ∃ z : L, B.equivFun z = c ∧ ∀ w : L, B.equivFun w = c → w = z := by
  refine ⟨B.equivFun.symm c, B.equivFun.apply_symm_apply c, ?_⟩
  intro w hw
  exact B.equivFun.injective (hw.trans (B.equivFun.apply_symm_apply c).symm)

