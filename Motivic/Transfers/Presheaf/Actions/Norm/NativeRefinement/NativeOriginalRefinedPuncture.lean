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
local notation "p₀" => Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) eN q heN B p.left W hW
local notation "p₁" => sourceNativeCoverMap (B.toScheme.presheaf.obj (Opposite.op ⊤)) O p₀
local notation "p₂" => sourceNativeCoverMap (O.toScheme.presheaf.obj (Opposite.op ⊤)) V p₁
local notation "a₀" => Scheme.originalAffineRefinedNativePuncture
  (U.left.presheaf.obj (Opposite.op ⊤)) eN q heN B a.left
local notation "a₁" => sourceNativeCoverMap (B.toScheme.presheaf.obj (Opposite.op ⊤)) O a₀
local notation "a₂" => sourceNativeCoverMap (O.toScheme.presheaf.obj (Opposite.op ⊤)) V a₁

/-- The final puncture is the original puncture restricted only on the same base. -/
def nativeOriginalRefinedPunctureSite : SmoothSite (Spec (.of k)) := by
  let : IsAffine ((a.left ≫ q) ⁻¹ᵁ B).toScheme :=
    Scheme.originalAffineRefinedNativePuncture_affine Γ(U.left, ⊤) eN q heN B a.left
  letI : Etale a₀ := inferInstance
  letI : Etale a₁ := sourceNativeCoverMap_etale Γ(B.toScheme, ⊤) O a₀
  letI : Etale a₂ := sourceNativeCoverMap_etale Γ(O.toScheme, ⊤) V a₁
  letI : IsAffine (boundaryBaseCoverOpen
      (boundaryLineProjection Γ(B.toScheme, ⊤)) a₀ ⊤ O).toScheme :=
    boundaryBaseCoverOpen_affine_instance _ a₀ ⊤ O
  letI : IsAffine (boundaryBaseCoverOpen
      (boundaryLineProjection Γ(O.toScheme, ⊤)) a₁ ⊤ V).toScheme :=
    boundaryBaseCoverOpen_affine_instance _ a₁ ⊤ V
  letI : Smooth a₂ := inferInstance
  letI : IsSeparated a₂ := inferInstance
  letI : QuasiCompact a₂ := inferInstance
  exact mkOverSmoothSite L₂ a₂

/-- Literal final puncture arrow into the entire original cylinder. -/
def nativeOriginalRefinedPunctureArrow : nativeOriginalRefinedPunctureSite U T e A a B O V ⟶
    a1Cylinder (.of k) U₂ :=
  (homMk a₂ rfl : nativeOriginalRefinedPunctureSite U T e A a B O V ⟶ L₂) ≫ (E₂).hom

/-- The underlying final puncture arrow is its literal native map followed by the same iso. -/
theorem nativeOriginalRefinedPunctureArrow_left :
    (nativeOriginalRefinedPunctureArrow U T e A a B O V).left = (a₂ ≫ (E₂).hom.left) := rfl

/-- The underlying final source arrow retains the same original containment witness. -/
theorem nativeOriginalRefinedSourceArrow_left
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V).left =
      sourceNativeCoverMap Γ(O.toScheme, ⊤) V
        (sourceNativeCoverMap Γ(B.toScheme, ⊤) O
          (Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤)
            (originalCylinderNativeIso U T e)
            (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
            (originalCylinderNativeIso_projection U T e) B p.left W hW)) ≫
        (nativeOriginalCylinderIso U T e B O V).hom.left := rfl

/-- The literal final puncture arrow is étale, using its already restricted map. -/
theorem nativeOriginalRefinedPunctureArrow_etale :
    Etale (nativeOriginalRefinedPunctureArrow U T e A a B O V).left := by
  let : Etale a₀ := inferInstance
  let : Etale a₁ := sourceNativeCoverMap_etale Γ(B.toScheme, ⊤) O a₀
  let : Etale a₂ := sourceNativeCoverMap_etale Γ(O.toScheme, ⊤) V a₁
  exact (inferInstance : Etale (a₂ ≫ (E₂).hom.left))

/-- The literal final source arrow is étale, retaining its original containment witness. -/
theorem nativeOriginalRefinedSourceArrow_etale
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    Etale (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V).left := by
  let p0 := Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B p.left W hW
  let p1 := sourceNativeCoverMap Γ(B.toScheme, ⊤) O p0
  let p2 := sourceNativeCoverMap Γ(O.toScheme, ⊤) V p1
  let : Etale p0 := Scheme.originalAffineRefinedNativeMap_etale
    Γ(U.left, ⊤) eN q heN B p.left W hW
  let : Etale p1 := sourceNativeCoverMap_etale Γ(B.toScheme, ⊤) O p0
  let : Etale p2 := sourceNativeCoverMap_etale Γ(O.toScheme, ⊤) V p1
  exact (inferInstance : Etale (p2 ≫ (nativeOriginalCylinderIso U T e B O V).hom.left))

/-- Underlying final-puncture restriction to the original open representative. -/
def nativeOriginalRefinedPunctureRestrictionScheme :
    (nativeOriginalRefinedPunctureSite U T e A a B O V).left ⟶ A.left :=
  (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) a₁ ⊤ V).ι ≫
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) a₀ ⊤ O).ι ≫
      ((a.left ≫ q) ⁻¹ᵁ B).ι

/-- The puncture square commutes with its unchanged original map. -/
theorem nativeOriginalRefinedPunctureRestriction_square :
    nativeOriginalRefinedPunctureRestrictionScheme U T e A a B O V ≫ a.left =
      (nativeOriginalRefinedPunctureArrow U T e A a B O V).left ≫ (h₂).left := by
  let i₁ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) a₀ ⊤ O).ι
  let i₂ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) a₁ ⊤ V).ι
  let τB := nativeAffineLineRestriction Γ(U.left, ⊤) B.ι
  let τO := nativeAffineLineRestriction Γ(B.toScheme, ⊤) O.ι
  let τV := nativeAffineLineRestriction Γ(O.toScheme, ⊤) V.ι
  have hV : a₂ ≫ τV = i₂ ≫ a₁ := sourceNativeCoverMap_coordinate _ V a₁
  have hO : a₁ ≫ τO = i₁ ≫ a₀ := sourceNativeCoverMap_coordinate _ O a₀
  have hB : a₀ ≫ τB = ((a.left ≫ q) ⁻¹ᵁ B).ι ≫ a.left ≫ (eN).hom := by
    have hc : (Scheme.originalAffineRefinedTargetIso Γ(U.left, ⊤) eN q heN B).hom ≫
        τB = (q ⁻¹ᵁ B).ι ≫ (eN).hom :=
      Scheme.originalAffineRefinedTargetIso_coordinate Γ(U.left, ⊤) eN q heN B
    have hr := morphismRestrict_ι a.left (q ⁻¹ᵁ B)
    exact (Category.assoc (a.left ∣_ (q ⁻¹ᵁ B))
        (Scheme.originalAffineRefinedTargetIso Γ(U.left, ⊤) eN q heN B).hom τB).trans
      ((congrArg (fun m => (a.left ∣_ (q ⁻¹ᵁ B)) ≫ m) hc).trans
        ((Category.assoc (a.left ∣_ (q ⁻¹ᵁ B)) (q ⁻¹ᵁ B).ι (eN).hom).symm.trans
          ((congrArg (fun m => m ≫ (eN).hom) hr).trans
            (Category.assoc ((a.left ≫ q) ⁻¹ᵁ B).ι a.left (eN).hom))))
  exact threeRestrictionSquares a₂ a₁ a₀ a.left i₂ i₁ ((a.left ≫ q) ⁻¹ᵁ B).ι
    τV τO τB eN ((forgetScheme (Spec (.of k))).mapIso E₂) hV hO hB

/-- The unchanged original-puncture inclusion in the actual smooth site. -/
def nativeOriginalRefinedPunctureRestriction :
    nativeOriginalRefinedPunctureSite U T e A a B O V ⟶ A :=
  homMk (nativeOriginalRefinedPunctureRestrictionScheme U T e A a B O V) (by
    rw [← MorphismProperty.Over.w a, ← Category.assoc,
      nativeOriginalRefinedPunctureRestriction_square, Category.assoc, MorphismProperty.Over.w,
      MorphismProperty.Over.w])

@[reassoc]
theorem nativeOriginalRefinedPunctureRestriction_comp :
    nativeOriginalRefinedPunctureRestriction U T e A a B O V ≫ a =
      nativeOriginalRefinedPunctureArrow U T e A a B O V ≫ h₂ := by
  apply MorphismProperty.Over.Hom.ext
  exact nativeOriginalRefinedPunctureRestriction_square U T e A a B O V


end AlgebraicGeometry.Scheme.SmoothSite
