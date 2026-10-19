/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.Basic

/-!
# Consumers of the product-diagonal decomposition

The isomorphism, coordinate formulas, and Cartesian diagonal square work for
arbitrary schemes. Only flatness of the remaining pair requires flatness of
the parameter map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProductDiagonal

universe u

namespace MotivicTest.ProductDiagonal

variable {S Y T : Scheme.{u}} (y : Y ⟶ S) (t : T ⟶ S)

example : pullback (pullback.fst y y ≫ y) t ≅
    pullback (pullback.diagonal t) (parameterPair y t) := quotientIso y t

example :
    (quotientIso y t).hom ≫ inclusion y t ≫
      pullback.fst (productBase y t) (productBase y t) ≫ pullback.fst y t =
        pullback.fst _ t ≫ pullback.fst y y := quotientIso_hom_first y t

example :
    (quotientIso y t).hom ≫ inclusion y t ≫
      pullback.snd (productBase y t) (productBase y t) ≫ pullback.fst y t =
        pullback.fst _ t ≫ pullback.snd y y := quotientIso_hom_second y t

example :
    (quotientIso y t).hom ≫ pullback.fst (pullback.diagonal t) (parameterPair y t) =
      pullback.snd _ t := quotientIso_hom_parameter y t

example [Flat t] : Flat (remainingYPair y t) := inferInstance

example :
    remainingYPair y t ≫ pullback.fst y y = inclusion y t ≫
      pullback.fst (productBase y t) (productBase y t) ≫ pullback.fst y t :=
  remainingYPair_fst y t

example :
    remainingYPair y t ≫ pullback.snd y y = inclusion y t ≫
      pullback.snd (productBase y t) (productBase y t) ≫ pullback.fst y t :=
  remainingYPair_snd y t

example : fullDiagonalLift y t ≫ inclusion y t = pullback.diagonal (productBase y t) :=
  fullDiagonalLift_inclusion y t

example : IsPullback (pullback.fst y t) (fullDiagonalLift y t)
    (pullback.diagonal y) (remainingYPair y t) := fullDiagonalLift_isPullback y t

example : pullback y t ≅ pullback (pullback.diagonal y) (remainingYPair y t) :=
  (fullDiagonalLift_isPullback y t).isoPullback


end MotivicTest.ProductDiagonal
