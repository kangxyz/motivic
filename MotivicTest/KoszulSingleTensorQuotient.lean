/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulSingleTensorQuotient

/-!
# Consumers of the one-element tensor quotient comparison

These examples use an arbitrary nonnegative complex and the actual scalar
quotient comparison. The regularity assumption concerns its terms alone.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory
open Motivic.Koszul

variable {R : Type u} [CommRing R] (a : R) (K : ChainComplex (ModuleCat.{u} R) ℕ)

example (n : ℕ) (x : K.X n) :
    (quotientProjection a K).f n x = Submodule.Quotient.mk x := rfl

example : HomologicalComplex.tensorObj (singleComplex R a) K ⟶ quotientComplex a K :=
  tensorAugmentation a K

example (ha : ∀ n, IsSMulRegular (K.X n) a) : QuasiIso (tensorAugmentation a K) :=
  tensorAugmentation_quasiIso_of_regular a K ha

example (ha : ∀ n, IsSMulRegular (K.X n) a) (n : ℕ) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).homology n ≅
      (quotientComplex a K).homology n := by
  letI := tensorAugmentation_quasiIso_of_regular a K ha
  exact isoOfQuasiIsoAt (tensorAugmentation a K) n

example (ha : ∀ n, IsSMulRegular (K.X n) a) (n : ℕ)
    (h : (quotientComplex a K).ExactAt n) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).ExactAt n := by
  have := tensorAugmentation_quasiIso_of_regular a K ha
  exact (exactAt_iff_of_quasiIsoAt (tensorAugmentation a K) n).mpr h
