/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Normal
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSource
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Normal integral geometry of the original affine-parameter projective line

The canonical projective base-change square identifies the literal target
product with P1 over the original parameter's coordinate ring. Its native
projection equations and stalk isomorphisms retain the original scheme maps.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.AffineParameterNormal`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.RelativeAffineLineGraphNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.RelativeProjectiveLine

/-- A normal integral Noetherian affine parameter gives the original projective
pullback integral Noetherian geometry and integrally closed original stalks. -/
theorem affineParameterPullback_normal
    (R : Type u) [CommRing R] {T : Scheme.{u}} [IsAffine T]
    [IsDomain Γ(T, ⊤)] [IsIntegrallyClosed Γ(T, ⊤)] [IsNoetherianRing Γ(T, ⊤)]
    (b : T ⟶ Spec (.of R)) :
    IsIntegral (pullback b (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ∧
      IsNoetherian (pullback b (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ∧
      ∀ x : (pullback b (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) : Scheme.{u}),
        IsIntegrallyClosed
          ((pullback b (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).presheaf.stalk x) := by
  let E := (Scheme.ConstantCurve.affineSourceProjectiveSquare
    R (ULift.{u} (Fin 2)) b).flip.isoPullback
  let : IsNoetherian (ProjectiveSpace Γ(T, ⊤) (ULift.{u} (Fin 2))) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (ProjectiveSpace.toSpec Γ(T, ⊤) (ULift.{u} (Fin 2)))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (ProjectiveSpace.toSpec Γ(T, ⊤) (ULift.{u} (Fin 2))) }
  refine ⟨IsIntegral.of_isIso E.hom, ?_, ?_⟩
  · exact
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian E.inv
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace E.inv }
  · intro x
    exact IsIntegrallyClosed.of_equiv (asIso (E.inv.stalkMap x)).commRingCatIsoToRingEquiv

end AlgebraicGeometry.RelativeProjectiveLine
