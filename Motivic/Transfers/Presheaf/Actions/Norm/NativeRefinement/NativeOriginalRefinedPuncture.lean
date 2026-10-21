/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.NativeOriginalRefinedSource
/-! # The original puncture and literal final-arrow identities and étaleness -/

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
  (A Y : SmoothSite (Spec (.of k))) [IsAffine A.left]
  (a : A ⟶ T) [IsOpenImmersion a.left] (p : Y ⟶ T) [Etale p.left]
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (W : Y.left.Opens) [IsAffine W.toScheme]

local notation "q" => Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e
local notation "eN" => originalCylinderNativeIso U T e
local notation "heN" => originalCylinderNativeIso_projection U T e

variable (hW : W ≤ p.left ⁻¹ᵁ (q ⁻¹ᵁ B))
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

local notation "U₂" => nativeOriginalBaseSite U B O V
local notation "L₂" => nativeOriginalLineSite U B O V
local notation "E₂" => nativeOriginalCylinderIso U T e B O V
local notation "h₂" => nativeOriginalWholeCylinderMap U T e B O V
/-- The final puncture is the original puncture restricted only on the same base. -/
def nativeOriginalRefinedPunctureSite : SmoothSite (Spec (.of k)) :=
  @originalAffineRefinedPunctureSite (Spec (.of k)) Γ(U.left, ⊤)
    T.left A.left eN q heN B inferInstance a.left O inferInstance V inferInstance
    (nativeOriginalLineSite U B O V).hom
    (nativeOriginalLineSite U B O V).prop.1.1
    (nativeOriginalLineSite U B O V).prop.1.2
    (nativeOriginalLineSite U B O V).prop.2 inferInstance inferInstance

/-- Literal final puncture arrow into the entire original cylinder. -/
def nativeOriginalRefinedPunctureArrow : nativeOriginalRefinedPunctureSite U T e A a B O V ⟶
    a1Cylinder (.of k) U₂ := by
  let f := @affineEtaleOverArrow (Spec (.of k))
      (originalAffineRefinedPunctureScheme Γ(U.left, ⊤) eN q heN B a.left O V)
      (originalAffineRefinedPunctureScheme_affine Γ(U.left, ⊤) eN q heN B a.left O V)
      (nativeOriginalLineSite U B O V)
      (inferInstance : IsAffine (Spec (.of (Polynomial Γ(V.toScheme, ⊤)))))
      (originalAffineRefinedPunctureMap Γ(U.left, ⊤) eN q heN B a.left O V)
      (originalAffineRefinedPunctureMap_etale Γ(U.left, ⊤) eN q heN B a.left O V)
  exact f ≫ (nativeOriginalCylinderIso U T e B O V).hom

/-- The underlying final puncture arrow is its literal native map followed by the same iso. -/
theorem nativeOriginalRefinedPunctureArrow_left :
    (nativeOriginalRefinedPunctureArrow U T e A a B O V).left =
      originalAffineRefinedPunctureMap Γ(U.left, ⊤) eN q heN B a.left O V ≫
        (E₂).hom.left := rfl

/-- The underlying final source arrow retains the same original containment witness. -/
theorem nativeOriginalRefinedSourceArrow_left
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V).left =
      originalAffineRefinedSourceMap Γ(U.left, ⊤) eN q heN B p.left W hW O V ≫
        (nativeOriginalCylinderIso U T e B O V).hom.left := rfl

/-- The literal final puncture arrow is étale, using its already restricted map. -/
theorem nativeOriginalRefinedPunctureArrow_etale :
    Etale (nativeOriginalRefinedPunctureArrow U T e A a B O V).left := by
  let h := @affineEtaleOverArrow_comp_iso_etale (Spec (.of k))
      (originalAffineRefinedPunctureScheme Γ(U.left, ⊤) eN q heN B a.left O V)
      (originalAffineRefinedPunctureScheme_affine Γ(U.left, ⊤) eN q heN B a.left O V)
      (nativeOriginalLineSite U B O V)
      (inferInstance : IsAffine (Spec (.of (Polynomial Γ(V.toScheme, ⊤)))))
      (originalAffineRefinedPunctureMap Γ(U.left, ⊤) eN q heN B a.left O V)
      (originalAffineRefinedPunctureMap_etale Γ(U.left, ⊤) eN q heN B a.left O V)
      (a1Cylinder (.of k) (nativeOriginalBaseSite U B O V))
      (nativeOriginalCylinderIso U T e B O V)
  exact h

/-- The literal final source arrow is étale, retaining its original containment witness. -/
theorem nativeOriginalRefinedSourceArrow_etale
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    Etale (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V).left := by
  let h := @affineEtaleOverArrow_comp_iso_etale (Spec (.of k))
      (originalAffineRefinedSourceScheme Γ(U.left, ⊤) eN q heN B p.left W hW O V)
      (originalAffineRefinedSourceScheme_affine Γ(U.left, ⊤) eN q heN B p.left W hW O V)
      (nativeOriginalLineSite U B O V)
      (inferInstance : IsAffine (Spec (.of (Polynomial Γ(V.toScheme, ⊤)))))
      (originalAffineRefinedSourceMap Γ(U.left, ⊤) eN q heN B p.left W hW O V)
      (originalAffineRefinedSourceMap_etale Γ(U.left, ⊤) eN q heN B p.left W hW O V)
      (a1Cylinder (.of k) (nativeOriginalBaseSite U B O V))
      (nativeOriginalCylinderIso U T e B O V)
  exact h

/-- Underlying final-puncture restriction to the original open representative. -/
def nativeOriginalRefinedPunctureRestrictionScheme :
    (nativeOriginalRefinedPunctureSite U T e A a B O V).left ⟶ A.left :=
  originalAffineRefinedPunctureRestrictionMap Γ(U.left, ⊤) eN q heN B a.left O V

/-- The puncture square commutes with its unchanged original map. -/
theorem nativeOriginalRefinedPunctureRestriction_square :
    nativeOriginalRefinedPunctureRestrictionScheme U T e A a B O V ≫ a.left =
      (nativeOriginalRefinedPunctureArrow U T e A a B O V).left ≫ (h₂).left :=
  originalAffineRefinedPunctureRestriction_square Γ(U.left, ⊤) eN q heN B a.left O V
    ((forgetScheme (Spec (.of k))).mapIso E₂)

/-- The unchanged original-puncture inclusion in the actual smooth site. -/
def nativeOriginalRefinedPunctureRestriction :
    nativeOriginalRefinedPunctureSite U T e A a B O V ⟶ A :=
  restrictionOfSquare (nativeOriginalRefinedPunctureRestrictionScheme U T e A a B O V)
    a (nativeOriginalRefinedPunctureArrow U T e A a B O V ≫ h₂)
    (nativeOriginalRefinedPunctureRestriction_square U T e A a B O V)

@[reassoc]
theorem nativeOriginalRefinedPunctureRestriction_comp :
    nativeOriginalRefinedPunctureRestriction U T e A a B O V ≫ a =
      nativeOriginalRefinedPunctureArrow U T e A a B O V ≫ h₂ :=
  restrictionOfSquare_comp (nativeOriginalRefinedPunctureRestrictionScheme U T e A a B O V)
    a (nativeOriginalRefinedPunctureArrow U T e A a B O V ≫ h₂)
    (nativeOriginalRefinedPunctureRestriction_square U T e A a B O V)


end AlgebraicGeometry.Scheme.SmoothSite
