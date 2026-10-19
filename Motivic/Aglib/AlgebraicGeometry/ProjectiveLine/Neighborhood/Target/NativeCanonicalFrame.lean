/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.MarkedBaseChange
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.AffineMarkedCoordinateFrame

/-! # The one canonical target marked frame after the common coefficient restriction

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeCanonicalFrame`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeSectionPair`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Hom Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R)))
  [IsFinite (z ≫ boundaryLineProjection R)]

/-- Choose the canonical marked frame once, after the common coefficient restriction.
It is a frame on the original marked scheme, available unchanged to both producers. -/
def targetNativeCanonicalFrame :
    SheafOfModules.unit (pullback (boundaryLineProjection (Γ(O.toScheme, ⊤)))
      (targetNativeMarked R O z ≫ boundaryLineProjection (Γ(O.toScheme, ⊤)))).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (boundaryLineProjection Γ(O.toScheme, ⊤))
        (targetNativeMarked R O z)) := by
  have : IsAffine ((z ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme :=
    isAffine_of_isAffineHom ((z ≫ boundaryLineProjection R) ∣_ O)
  exact affineMarkedCoordinateFrame (Γ(O.toScheme, ⊤)) (targetNativeMarked R O z)

end AlgebraicGeometry.RelativeProjectiveLine
