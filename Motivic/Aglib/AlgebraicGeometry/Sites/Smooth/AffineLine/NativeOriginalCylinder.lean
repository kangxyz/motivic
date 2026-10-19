/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalLineRestriction
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CartesianCylinderIso
/-! # The actual whole cylinder over the same native coefficient base

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalCylinder`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`NativeRefinement.NativeOriginalRefinedSource`.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ a1Cylinder (.of k) U)
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

local notation "m" => nativeOriginalLineMap U T e B O V
local notation "q" => polynomialProjection
  (CommRingCat.of (V.toScheme.presheaf.obj (Opposite.op ⊤)))
local notation "l" => nativeOriginalCoefficientMap U B O V
local notation "t" => nativeOriginalFinalFieldMap U B O V

/-- The whole-cylinder comparison instantiates the generic Cartesian adapter. -/
def nativeOriginalCylinderIso :
    nativeOriginalLineSite U B O V ≅ a1Cylinder (.of k) (nativeOriginalBaseSite U B O V) :=
  cartesianCylinderIso (.of k) (nativeOriginalBaseInclusion U B O V)
    (nativeOriginalLineRestriction U T e B O V) (nativeOriginalLineProjection U B O V)
    e (nativeOriginalRestriction_isPullback U T e B O V)

/-- The comparison preserves the actual native base projection. -/
theorem nativeOriginalCylinderIso_projection :
    (nativeOriginalCylinderIso U T e B O V).hom ≫
      a1Projection (.of k) (nativeOriginalBaseSite U B O V) =
        nativeOriginalLineProjection U B O V :=
  cartesianCylinderIso_projection (.of k) (nativeOriginalBaseInclusion U B O V)
    (nativeOriginalLineRestriction U T e B O V) (nativeOriginalLineProjection U B O V)
    e (nativeOriginalRestriction_isPullback U T e B O V)

/-- The second coordinate is inherited from the original cylinder. -/
theorem nativeOriginalCylinderIso_coordinate :
    (nativeOriginalCylinderIso U T e B O V).hom.left ≫
      pullback.snd t (polynomialProjection (.of k)) =
        m ≫ e.hom.left ≫ pullback.snd U.hom (polynomialProjection (.of k)) :=
  cartesianCylinderIso_coordinate (.of k) (nativeOriginalBaseInclusion U B O V)
    (nativeOriginalLineRestriction U T e B O V) (nativeOriginalLineProjection U B O V)
    e (nativeOriginalRestriction_isPullback U T e B O V)

/-- The whole-cylinder identification preserves the literal original restriction. -/
theorem nativeOriginalCylinderIso_comp :
    (nativeOriginalCylinderIso U T e B O V).hom ≫
      a1Map (.of k) (nativeOriginalBaseInclusion U B O V) =
        nativeOriginalLineRestriction U T e B O V ≫ e.hom :=
  cartesianCylinderIso_comp (.of k) (nativeOriginalBaseInclusion U B O V)
    (nativeOriginalLineRestriction U T e B O V) (nativeOriginalLineProjection U B O V)
    e (nativeOriginalRestriction_isPullback U T e B O V)

/-- The map required by the original whole-cylinder lifting consumer. -/
def nativeOriginalWholeCylinderMap :
    a1Cylinder (.of k) (nativeOriginalBaseSite U B O V) ⟶ T :=
  (nativeOriginalCylinderIso U T e B O V).inv ≫ nativeOriginalLineRestriction U T e B O V

/-- This is a restriction of the entire original cylinder along the original base. -/
theorem nativeOriginalWholeCylinderMap_comp :
    nativeOriginalWholeCylinderMap U T e B O V ≫ e.hom =
      a1Map (.of k) (nativeOriginalBaseInclusion U B O V) := by
  rw [nativeOriginalWholeCylinderMap, Category.assoc,
    ← nativeOriginalCylinderIso_comp, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.SmoothSite
