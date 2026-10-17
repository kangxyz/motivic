module
import Motivic.Aglib.RingTheory.SimultaneousResidueLinearProjection
import Mathlib.RingTheory.Derivation.Basic

/-! # Simultaneous actual function selection from residue-field derivations -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open Matrix

example {k R : Type} [Field k] [Infinite k] [CommRing R] [Algebra k R]
    {ι : Type} [Finite ι] {d m : ℕ}
    (K : ι → Type) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    [∀ i, Module R (K i)]
    (D : (i : ι) → Fin d → Derivation k R (K i)) (g : Fin m → R)
    (hD : ∀ i, Function.Surjective
      (Matrix.mulVec (fun a b => D i a (g b) : Matrix (Fin d) (Fin m) (K i)))) :
    ∃ B : Matrix (Fin m) (Fin d) k,
      ∀ i, Matrix.det (fun a b => D i a (∑ j, B j b • g j)) ≠ 0 := by
  obtain ⟨B, hB⟩ := Matrix.exists_simultaneous_residue_linear_projection k K
    (fun i a b => D i a (g b)) hD
  refine ⟨B, fun i => ?_⟩
  convert hB i using 1
  congr 1
  ext a b
  simp only [map_sum, Derivation.map_smul, Matrix.mul_apply, Matrix.map_apply]
  simp [Algebra.smul_def, mul_comm]
