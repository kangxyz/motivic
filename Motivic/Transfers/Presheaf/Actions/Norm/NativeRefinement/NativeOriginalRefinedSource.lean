/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalCylinder
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
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

/-- Compose three actual restriction squares and cancel the two coordinate isomorphisms. -/
theorem threeRestrictionSquares
    {C : Type*} [Category C] {Y₂ Y₁ Y₀ Y L₂ L₁ L₀ N T D : C}
    (p₂ : Y₂ ⟶ L₂) (p₁ : Y₁ ⟶ L₁) (p₀ : Y₀ ⟶ L₀) (p : Y ⟶ T)
    (i₂ : Y₂ ⟶ Y₁) (i₁ : Y₁ ⟶ Y₀) (i₀ : Y₀ ⟶ Y)
    (τV : L₂ ⟶ L₁) (τO : L₁ ⟶ L₀) (τB : L₀ ⟶ N)
    (e : T ≅ N) (f : L₂ ≅ D)
    (hV : p₂ ≫ τV = i₂ ≫ p₁) (hO : p₁ ≫ τO = i₁ ≫ p₀)
    (hB : p₀ ≫ τB = i₀ ≫ p ≫ e.hom) :
    (i₂ ≫ i₁ ≫ i₀) ≫ p =
      (p₂ ≫ f.hom) ≫ (f.inv ≫ ((τV ≫ τO ≫ τB) ≫ e.inv)) := by
  have hc : p₂ ≫ ((τV ≫ τO ≫ τB) ≫ e.inv) = i₂ ≫ i₁ ≫ i₀ ≫ p := by
    calc
      _ = i₂ ≫ p₁ ≫ τO ≫ τB ≫ e.inv := by
        simpa only [Category.assoc] using congrArg (fun m => m ≫ τO ≫ τB ≫ e.inv) hV
      _ = i₂ ≫ i₁ ≫ p₀ ≫ τB ≫ e.inv := by
        simpa only [Category.assoc] using congrArg (fun m => i₂ ≫ m ≫ τB ≫ e.inv) hO
      _ = _ := by
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun m => i₂ ≫ i₁ ≫ m ≫ e.inv) hB
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc.symm

/-- Compose an actual smooth-site structure with an already verified morphism. -/
def mkOverSmoothSite {S Y : Scheme.{u}} (X : SmoothSite S) (p : Y ⟶ X.left)
    [Smooth p] [IsSeparated p] [QuasiCompact p] : SmoothSite S :=
  mk (p ≫ X.hom)

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
    SmoothSite (Spec (.of k)) := by
  let p0 := Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B p.left W hW
  let p1 := sourceNativeCoverMap Γ(B.toScheme, ⊤) O p0
  let p2 := sourceNativeCoverMap Γ(O.toScheme, ⊤) V p1
  let line := nativeOriginalLineSite U B O V
  letI : Etale p0 := Scheme.originalAffineRefinedNativeMap_etale
    Γ(U.left, ⊤) eN q heN B p.left W hW
  letI : Etale p1 := sourceNativeCoverMap_etale Γ(B.toScheme, ⊤) O p0
  letI : Etale p2 := sourceNativeCoverMap_etale Γ(O.toScheme, ⊤) V p1
  letI : IsAffine (boundaryBaseCoverOpen
      (boundaryLineProjection Γ(B.toScheme, ⊤)) p0 ⊤ O).toScheme :=
    boundaryBaseCoverOpen_affine_instance _ p0 ⊤ O
  letI : IsAffine (boundaryBaseCoverOpen
      (boundaryLineProjection Γ(O.toScheme, ⊤)) p1 ⊤ V).toScheme :=
    boundaryBaseCoverOpen_affine_instance _ p1 ⊤ V
  letI : Smooth p2 := inferInstance
  letI : IsSeparated p2 := inferInstance
  letI : QuasiCompact p2 := inferInstance
  exact mkOverSmoothSite line p2


/-- Literal final source arrow into the entire original cylinder. -/
def nativeOriginalRefinedSourceArrow
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceSite U T e Y p B W hW O V ⟶
    a1Cylinder (.of k) (nativeOriginalBaseSite U B O V) := by
  let p0 := Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B p.left W hW
  let p1 := sourceNativeCoverMap Γ(B.toScheme, ⊤) O p0
  let p2 := sourceNativeCoverMap Γ(O.toScheme, ⊤) V p1
  exact
    (homMk p2 rfl : nativeOriginalRefinedSourceSite U T e Y p B W hW O V ⟶
      nativeOriginalLineSite U B O V) ≫ (nativeOriginalCylinderIso U T e B O V).hom

/-- Underlying final-source restriction to the original étale representative. -/
def nativeOriginalRefinedSourceRestrictionScheme
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    (nativeOriginalRefinedSourceSite U T e Y p B W hW O V).left ⟶ Y.left := by
  let p0 := Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B p.left W hW
  let p1 := sourceNativeCoverMap Γ(B.toScheme, ⊤) O p0
  exact
    (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p1 ⊤ V).ι ≫
      (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) p0 ⊤ O).ι ≫ W.ι

/-- The source square commutes with the original map, not a replacement map. -/
theorem nativeOriginalRefinedSourceRestriction_square
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceRestrictionScheme U T e Y p B W hW O V ≫ p.left =
      (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V).left ≫
        (nativeOriginalWholeCylinderMap U T e B O V).left := by
  let p0 := Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B p.left W hW
  let p1 := sourceNativeCoverMap Γ(B.toScheme, ⊤) O p0
  let p2 := sourceNativeCoverMap Γ(O.toScheme, ⊤) V p1
  let i₁ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(B.toScheme, ⊤)) p0 ⊤ O).ι
  let i₂ := (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p1 ⊤ V).ι
  let τB := nativeAffineLineRestriction Γ(U.left, ⊤) B.ι
  let τO := nativeAffineLineRestriction Γ(B.toScheme, ⊤) O.ι
  let τV := nativeAffineLineRestriction Γ(O.toScheme, ⊤) V.ι
  have hV : p2 ≫ τV = i₂ ≫ p1 := sourceNativeCoverMap_coordinate _ V p1
  have hO : p1 ≫ τO = i₁ ≫ p0 := sourceNativeCoverMap_coordinate _ O p0
  have hB : p0 ≫ τB = W.ι ≫ p.left ≫ ((originalCylinderNativeIso U T e)).hom :=
    Scheme.originalAffineRefinedNativeMap_coordinate _ (originalCylinderNativeIso U T e)
      (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
      (originalCylinderNativeIso_projection U T e) B p.left W hW
  exact threeRestrictionSquares p2 p1 p0 p.left i₂ i₁ W.ι τV τO τB
    (originalCylinderNativeIso U T e)
    ((forgetScheme (Spec (.of k))).mapIso (nativeOriginalCylinderIso U T e B O V)) hV hO hB

/-- The unchanged original-source open inclusion, now in the actual smooth site. -/
def nativeOriginalRefinedSourceRestriction
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceSite U T e Y p B W hW O V ⟶ Y :=
  homMk (nativeOriginalRefinedSourceRestrictionScheme U T e Y p B W hW O V) (by
    rw [← MorphismProperty.Over.w p, ← Category.assoc,
      nativeOriginalRefinedSourceRestriction_square, Category.assoc, MorphismProperty.Over.w,
      MorphismProperty.Over.w])

@[reassoc]
theorem nativeOriginalRefinedSourceRestriction_comp
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme] :
    nativeOriginalRefinedSourceRestriction U T e Y p B W hW O V ≫ p =
      nativeOriginalRefinedSourceArrow U T e Y p B W hW O V ≫
        nativeOriginalWholeCylinderMap U T e B O V := by
  apply MorphismProperty.Over.Hom.ext
  exact nativeOriginalRefinedSourceRestriction_square U T e Y p B W hW O V


end AlgebraicGeometry.Scheme.SmoothSite
