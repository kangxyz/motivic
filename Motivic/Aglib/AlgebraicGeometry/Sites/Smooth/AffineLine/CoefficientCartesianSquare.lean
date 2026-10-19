/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.AffineSpecSquare
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderNativeCoordinates
/-! # The original cylinder after the three retained coefficient restrictions

The native coefficient and line maps remain literal composites. Cartesian
pasting, rather than a comparison of composite global-section ring maps,
identifies the final whole line over the original base.

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CoefficientCartesianSquare`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`AffineLine.NativeOriginalBase`.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RelativeProjectiveLine Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ a1Cylinder (.of k) U)
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- The same three affine opens, with the final base in native spectrum form. -/
def nativeOriginalCoefficientMap : Spec Γ(V.toScheme, ⊤) ⟶ U.left :=
  (nativeAffineBaseRestriction Γ(O.toScheme, ⊤) V.ι ≫
    nativeAffineBaseRestriction Γ(B.toScheme, ⊤) O.ι ≫
    nativeAffineBaseRestriction Γ(U.left, ⊤) B.ι) ≫ U.left.isoSpec.inv

/-- Forget the three coefficient restrictions, then return to the original cylinder. -/
def nativeOriginalLineMap : Spec (.of (Polynomial Γ(V.toScheme, ⊤))) ⟶ T.left :=
  (nativeAffineLineRestriction Γ(O.toScheme, ⊤) V.ι ≫
    nativeAffineLineRestriction Γ(B.toScheme, ⊤) O.ι ≫
    nativeAffineLineRestriction Γ(U.left, ⊤) B.ι) ≫
      (AffineCoordinates.originalCylinderNativeIso U T e).inv

private theorem originalCylinderNativeIso_inv_projection :
    polynomialProjection (.of Γ(U.left, ⊤)) ≫ U.left.isoSpec.inv =
      (AffineCoordinates.originalCylinderNativeIso U T e).inv ≫
        (e.hom ≫ a1Projection (.of k) U).left := by
  apply (cancel_epi
    (AffineCoordinates.originalCylinderNativeIso U T e).hom).mp
  rw [← Category.assoc,
    AffineCoordinates.originalCylinderNativeIso_projection]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id]
  rfl

/-- The entire final native line is the pullback of the original cylinder along
its actual original-base open inclusion. No total-space open is selected. -/
theorem nativeOriginalCoefficient_isPullback :
    IsPullback (nativeOriginalLineMap U T e B O V)
      (polynomialProjection (.of Γ(V.toScheme, ⊤)))
      (e.hom ≫ a1Projection (.of k) U).left
      (nativeOriginalCoefficientMap U B O V) := by
  have H := (nativeAffineSpecSquare Γ(O.toScheme, ⊤) V.ι).paste_horiz
    ((nativeAffineSpecSquare Γ(B.toScheme, ⊤) O.ι).paste_horiz
      (nativeAffineSpecSquare Γ(U.left, ⊤) B.ι))
  apply H.of_iso (Iso.refl _)
    (AffineCoordinates.originalCylinderNativeIso U T e).symm
    (Iso.refl _) U.left.isoSpec.symm
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp,
      nativeOriginalLineMap]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · exact originalCylinderNativeIso_inv_projection U T e
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp,
      nativeOriginalCoefficientMap]
    rfl

end AlgebraicGeometry.Scheme.SmoothSite
