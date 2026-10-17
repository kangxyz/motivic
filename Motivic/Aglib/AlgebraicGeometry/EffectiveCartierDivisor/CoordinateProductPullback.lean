/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen

/-! # The actual source-times-boundary map and its literal coordinate pullback -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Actual change of the first product factor while retaining the full second factor. -/
def boundarySourceProductMap {S X V Y Z : Scheme.{u}}
    (q : X ⟶ S) (k : V ⟶ X) (p : Y ⟶ V) (z : Z ⟶ X) :
    pullback ((p ≫ k) ≫ q) (z ≫ q) ⟶ pullback (k ≫ q) (z ≫ q) :=
  pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _) (by
    simpa only [Category.assoc] using
      (pullback.condition (f := (p ≫ k) ≫ q) (g := z ≫ q)))

/-- The original product projection factors through the retained target product literally. -/
@[reassoc (attr := simp)]
theorem boundarySourceProductMap_comp {S X V Y Z : Scheme.{u}}
    (q : X ⟶ S) (k : V ⟶ X) (p : Y ⟶ V) (z : Z ⟶ X) :
    boundarySourceProductMap q k p z ≫ boundaryProductMap q k z =
      boundaryProductMap q (p ≫ k) z := by
  apply pullback.hom_ext <;>
    simp [boundarySourceProductMap, boundaryProductMap, Category.assoc]

/-- On the actual source product, the unchanged coordinate ratio is exactly the
pullback from the fixed target product under p × id_Z. -/
theorem boundaryCoordinateEndomorphism_sourceProduct
    (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
    {V Y : Scheme.{u}} (k : V ⟶ Spec (.of R[X])) (p : Y ⟶ V) :
    boundaryCoordinateEndomorphism R B z
        (boundaryProductMap (boundaryLineProjection R) (p ≫ k) (boundaryCoordinateMap R B z)) =
      unitEndomorphismPullback
        (boundarySourceProductMap (boundaryLineProjection R) k p (boundaryCoordinateMap R B z))
        (boundaryCoordinateEndomorphism R B z
          (boundaryProductMap (boundaryLineProjection R) k (boundaryCoordinateMap R B z))) :=
  boundaryCoordinateEndomorphism_of_factor R B z _ _ _ (boundarySourceProductMap_comp ..)

end AlgebraicGeometry.Scheme.Hom
