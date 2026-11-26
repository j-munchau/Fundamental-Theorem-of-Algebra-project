import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.AdjoinRoot

assert_not_imported Mathlib.Analysis.Complex.Polynomial.Basic

open Polynomial

example (K L : Type*) [Field K] [Field L] [Algebra K L]
    (B : Module.Basis (Fin 2) K L) (c : Fin 2 → K) :
    ∃ z : L, B.equivFun z = c ∧ ∀ w : L, B.equivFun w = c → w = z := by
  refine ⟨B.equivFun.symm c, B.equivFun.apply_symm_apply c, ?_⟩
  intro w hw
  exact B.equivFun.injective (hw.trans (B.equivFun.apply_symm_apply c).symm)

example (K : Type*) [Field K] (p : K[X]) :
    aeval (AdjoinRoot.root p) p = 0 := by
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

noncomputable def quadraticForI (K : Type*) [Field K] : K[X] :=
  X^2 + 1

example (K : Type*) [Field K] :
    (AdjoinRoot.root (quadraticForI K))^2 = -1 := by
  apply add_eq_zero_iff_eq_neg.mp
  calc
    (AdjoinRoot.root (quadraticForI K))^2 + 1 =
        AdjoinRoot.mk (quadraticForI K) (X^2 + 1) := by
      rw [RingHom.map_add, _root_.map_pow,
        AdjoinRoot.mk_X, RingHom.map_one]
    _ = 0 := AdjoinRoot.mk_self (f := quadraticForI K)

example (K : Type*) [Field K] (p : K[X])
    (hp : Irreducible p)
    (x : AdjoinRoot p) (hx : x ≠ 0) :
    ∃ y : AdjoinRoot p, x * y = 1 := by
  let : Fact (Irreducible p) := ⟨hp⟩
  exact ⟨x⁻¹, mul_inv_cancel₀ hx⟩
