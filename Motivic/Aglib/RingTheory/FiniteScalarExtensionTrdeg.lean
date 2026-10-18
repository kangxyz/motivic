/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Flat.Basic

/-! # Transcendence degree of an integral finite scalar extension -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u

attribute [local instance] rightAlgebra

/-- Finite extension of the ground field preserves transcendence degree of the
actual tensor domain. Faithfulness is proved from the literal tensor inclusion. -/
theorem trdeg_right_eq_of_finite
    (k R L : Type u) [Field k] [CommRing R] [Nontrivial R] [Field L]
    [Algebra k R] [Algebra k L] [Module.Finite k L] [IsDomain (R ⊗[k] L)] :
    Algebra.trdeg L (R ⊗[k] L) = Algebra.trdeg k R := by
  let S := R ⊗[k] L
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    (includeLeft_injective (R := k) (S := k) (A := R) (B := L)
      (algebraMap k L).injective)
  have hR : Algebra.trdeg k R = Algebra.trdeg k S := by
    simpa only [trdeg_eq_zero (R := R) (A := S), add_zero] using
      trdeg_add_eq k R (A := S)
  have hL : Algebra.trdeg L S = Algebra.trdeg k S := by
    simpa only [trdeg_eq_zero (R := k) (A := L), zero_add] using
      trdeg_add_eq k L (A := S)
  exact hL.trans hR.symm

end Algebra.TensorProduct
