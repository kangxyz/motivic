/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # The determinant of a rank-one update on a finite free module

Intended upstream module: `Aglib.LinearAlgebra.Determinant.RankOne`.
Incoming project consumers: `Motivic.Aglib.RingTheory.Norm.FiniteFree.MarkedFiber`.
-/

@[expose] public noncomputable section

namespace LinearMap

/-- The determinant lemma on the original finite free module, without any
freeness requirement on the kernel of the functional. -/
theorem det_id_add_smulRight
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] (ell : M →ₗ[R] R) (v : M) :
    LinearMap.det (LinearMap.id + ell.smulRight v) = 1 + ell v := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [← det_toMatrix b, map_add, toMatrix_id, toMatrix_smulRight,
    Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simpa only [dotProduct, Function.comp_apply, map_sum, map_smul, smul_eq_mul, mul_comm] using
    congrArg ell (b.sum_repr v)

end LinearMap
