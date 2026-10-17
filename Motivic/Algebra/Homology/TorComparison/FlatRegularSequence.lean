/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.FlatCoefficient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Ring-regular sequences on flat resolution terms

A weakly regular ring sequence stays weakly regular on every flat module.
This is proved on the actual successive ideal quotients, using their tensor
product descriptions and flatness. In particular it applies to every term of
an arbitrary projective resolution, without bounding the resolution or asking
for regularity on the module being resolved. It supplies the termwise
regularity needed for the regular-Koszul augmentation comparison.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Motivic.TorComparison

variable {R : Type u} [CommRing R]

/-- A ring-regular sequence is weakly regular on every flat coefficient module. -/
theorem weaklyRegular_of_flat_module (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Flat R M] (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    RingTheory.Sequence.IsWeaklyRegular M s := by
  constructor
  intro i hi
  let I := Ideal.ofList (s.take i)
  have hI : I • (⊤ : Submodule R R) = I :=
    (Ideal.smul_eq_mul I ⊤).trans I.mul_top
  have h : IsSMulRegular (R ⧸ I) s[i] := by
    have hprev := hs.regular_mod_prev i hi
    change IsSMulRegular (R ⧸ (I • (⊤ : Submodule R R))) s[i] at hprev
    rwa [hI] at hprev
  exact ((TensorProduct.quotTensorEquivQuotSMul M I).isSMulRegular_congr s[i]).mp
    (h.rTensor M)

/-- Every term of any genuine projective resolution inherits ring regularity,
regardless of regularity or projective dimension of the resolved module. -/
theorem weaklyRegular_projectiveResolution_terms (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (P.complex.X n) s :=
  weaklyRegular_of_flat_module (P.complex.X n) s hs

end Motivic.TorComparison
