/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalCylinder
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeCover
public import Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization
/-! # The same-witness final native source and its original restriction square -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ a1Cylinder (.of k) U)
  (Y : SmoothSite (Spec (.of k))) (p : Y ⟶ T) [Etale p.left]
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (W : Y.left.Opens) [IsAffine W.toScheme]

local notation "q" => Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e
local notation "eN" => originalCylinderNativeIso U T e
local notation "heN" => originalCylinderNativeIso_projection U T e

variable (hW : W ≤ p.left ⁻¹ᵁ (q ⁻¹ᵁ B))
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- The final affine source is exactly the twice-restricted original W. -/
def nativeOriginalRefinedSourceSite
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    SmoothSite (Spec (.of k)) :=
  @originalAffineRefinedSourceSite (Spec (.of k)) Γ(U.left, ⊤)
    T.left Y.left eN q heN B inferInstance p.left W inferInstance hW
    O inferInstance V inferInstance (nativeOriginalLineSite U B O V).hom
    (nativeOriginalLineSite U B O V).prop.1.1
    (nativeOriginalLineSite U B O V).prop.1.2
    (nativeOriginalLineSite U B O V).prop.2 inferInstance


/-- Literal final source arrow into the entire original cylinder. -/
def nativeOriginalRefinedSourceArrow
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceSite U T e Y p B W hW O V ⟶
    a1Cylinder (.of k) (nativeOriginalBaseSite U B O V) :=
  @affineEtaleOverArrow (Spec (.of k))
    (originalAffineRefinedSourceScheme Γ(U.left, ⊤) eN q heN B p.left W hW O V)
    (originalAffineRefinedSourceScheme_affine Γ(U.left, ⊤) eN q heN B p.left W hW O V)
    (nativeOriginalLineSite U B O V)
    (inferInstance : IsAffine (Spec (.of (Polynomial Γ(V.toScheme, ⊤)))))
    (originalAffineRefinedSourceMap Γ(U.left, ⊤) eN q heN B p.left W hW O V)
    (originalAffineRefinedSourceMap_etale Γ(U.left, ⊤) eN q heN B p.left W hW O V) ≫
      (nativeOriginalCylinderIso U T e B O V).hom

/-- Underlying final-source restriction to the original étale representative. -/
def nativeOriginalRefinedSourceRestrictionScheme
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    (nativeOriginalRefinedSourceSite U T e Y p B W hW O V).left ⟶ Y.left :=
  originalAffineRefinedSourceRestrictionMap Γ(U.left, ⊤) eN q heN B p.left W hW O V

/-- The source square commutes with the original map, not a replacement map. -/
theorem nativeOriginalRefinedSourceRestriction_square
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceRestrictionScheme U T e Y p B W hW O V ≫ p.left =
      (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V).left ≫
        (nativeOriginalWholeCylinderMap U T e B O V).left :=
  originalAffineRefinedSourceRestriction_square Γ(U.left, ⊤) eN q heN B p.left W hW O V
    ((forgetScheme (Spec (.of k))).mapIso (nativeOriginalCylinderIso U T e B O V))

/-- The unchanged original-source open inclusion, now in the actual smooth site. -/
def nativeOriginalRefinedSourceRestriction
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceSite U T e Y p B W hW O V ⟶ Y :=
  restrictionOfSquare (nativeOriginalRefinedSourceRestrictionScheme U T e Y p B W hW O V)
    p (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V ≫
      nativeOriginalWholeCylinderMap U T e B O V)
    (nativeOriginalRefinedSourceRestriction_square U T e Y p B W hW O V)

@[reassoc]
theorem nativeOriginalRefinedSourceRestriction_comp
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceRestriction U T e Y p B W hW O V ≫ p =
      nativeOriginalRefinedSourceArrow U T e Y p B W hW O V ≫
        nativeOriginalWholeCylinderMap U T e B O V :=
  restrictionOfSquare_comp (nativeOriginalRefinedSourceRestrictionScheme U T e Y p B W hW O V)
    p (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V ≫
      nativeOriginalWholeCylinderMap U T e B O V)
    (nativeOriginalRefinedSourceRestriction_square U T e Y p B W hW O V)


end AlgebraicGeometry.Scheme.SmoothSite
