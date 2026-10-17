/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryCanonicalCoordinate

/-! # Exact coordinate naturality of the original étale boundary graph -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The actual neighborhood coordinate, followed by its actual ideal inclusion,
is the pullback of the target coordinate. The full Z scheme is unchanged. -/
theorem neighborhoodBoundaryIdealIso_coordinate
    (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R[X])) [Flat p] (s : Spec (.of B) ⟶ Y)
    (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z)) :
    (neighborhoodBoundaryIdealIso R B z p s h H).hom ≫
        idealInclusion (boundaryGraphSource (boundaryLineProjection R) p
          (boundaryCoordinateMap R B z) s h) =
      (pullbackUnitIso (boundaryProductMap (boundaryLineProjection R) p
        (boundaryCoordinateMap R B z))).inv ≫
      (Scheme.Modules.pullback (boundaryProductMap (boundaryLineProjection R) p
        (boundaryCoordinateMap R B z))).map
        ((boundaryCoordinateIdealIso R B z).hom ≫
          idealInclusion (boundaryGraphTarget (boundaryLineProjection R)
            (boundaryCoordinateMap R B z))) ≫
      (pullbackUnitIso (boundaryProductMap (boundaryLineProjection R) p
        (boundaryCoordinateMap R B z))).hom := by
  dsimp only [neighborhoodBoundaryIdealIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom]
  simp only [Category.assoc]
  rw [idealPullbackMap_inclusion]
  rw [Functor.map_comp]
  rfl

/-- The compactification ideal coordinate is exactly the same neighborhood coordinate,
transported along the unchanged product comparison. -/
theorem compactificationBoundaryIdealIso_coordinate
    (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
    {C Y : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
    (j : Y ⟶ C) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of R[X])) [Flat p]
    (hq : j ≫ q = p ≫ boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z)) :
    let eP : pullback (j ≫ q) (s ≫ j ≫ q) ≅
        pullback (p ≫ boundaryLineProjection R)
          (boundaryCoordinateMap R B z ≫ boundaryLineProjection R) :=
      pullback.congrHom hq (by rw [hq, ← Category.assoc, h])
    (compactificationBoundaryIdealIso R B z q j p hq s h H).hom ≫
      Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q j))
        (graphBoundaryRestriction q j s) =
      (pullbackUnitIso eP.hom).inv ≫ (Scheme.Modules.pullback eP.hom).map
        ((neighborhoodBoundaryIdealIso R B z p s h H).hom ≫
          idealInclusion (boundaryGraphSource (boundaryLineProjection R) p
            (boundaryCoordinateMap R B z) s h)) ≫ (pullbackUnitIso eP.hom).hom := by
  dsimp only [compactificationBoundaryIdealIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc]
  unfold Modules.Hom.pullbackToUnit
  erw [← idealPullbackMap_inclusion (compactificationGraph q j)
    (restrictedBoundaryGraph q j s) (graphBoundaryRestriction q j s) s
    (compactificationGraph_boundary_isPullback q j s).w]
  rw [IsIso.inv_hom_id_assoc]
  rw [idealPullbackMap_inclusion, Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Hom
