/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.NativeCoefficientFieldLifting
public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.NativeOriginalRefinedPuncture
public import Motivic.Transfers.Presheaf.Actions.Norm.RefinedSectionChoice
/-! # Literal final native cover arrows in the original smooth site

Every arrow below uses the existing affine source W and the existing coefficient
opens. The final cover is transported onto the whole original cylinder, and its
maps back to the original representatives are the literal open inclusions.
-/

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

/-- Transport a chosen lift through the same target isomorphism. -/
private theorem lift_comp_iso_eq {C : Type*} [Category C] {Z Y L T : C}
    (b : Z ⟶ Y) (a : Y ⟶ L) (x : Z ⟶ T) (e : L ≅ T)
    (h : b ≫ a = x ≫ e.inv) : b ≫ (a ≫ e.hom) = x := by
  rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id]

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

/-- The original full marked square makes the exact final arrows a cover of the
whole cylinder over the retained common coefficient open. -/
theorem nativeOriginalRefinedCover_mem_nisnevichTopology
    (hW : W ≤ p.left ⁻¹ᵁ
      ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))
    (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
    {Z : Scheme.{u}} (z : Z ⟶ T.left) [IsClosedImmersion z]
    (hz : Set.range z = (Set.range a.left)ᶜ)
    (t :
      ((z ≫ Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
        ⁻¹ᵁ B).toScheme ⟶
      W.toScheme)
    (H : IsPullback t (𝟙 _)
      (p.left.resLE
        ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B) W hW)
      (z ∣_ ((Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e) ⁻¹ᵁ B))) :
    Sieve.ofTwoArrows
      (nativeOriginalRefinedPunctureArrow U T e A a B O V)
      (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V) ∈
        nisnevichTopology (Spec (.of k)) (a1Cylinder (.of k) (nativeOriginalBaseSite U B O V)) := by
  let p0 := Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B p.left W hW
  let p1 := sourceNativeCoverMap Γ(B.toScheme, ⊤) O p0
  let p2 := sourceNativeCoverMap Γ(O.toScheme, ⊤) V p1
  let a0 := Scheme.originalAffineRefinedNativePuncture Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B a.left
  let a1 := sourceNativeCoverMap Γ(B.toScheme, ⊤) O a0
  let a2 := sourceNativeCoverMap Γ(O.toScheme, ⊤) V a1
  let eS : Spec (.of (Polynomial Γ(V.toScheme, ⊤))) ≅
      (a1Cylinder (.of k) (nativeOriginalBaseSite U B O V)).left :=
    (forgetScheme (Spec (.of k))).mapIso (nativeOriginalCylinderIso U T e B O V)
  let z₀ := Scheme.originalAffineRefinedNativeMarked Γ(U.left, ⊤)
    (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B z
  let : IsAffine
      ((a.left ≫ Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
        ⁻¹ᵁ B).toScheme
      :=
    Scheme.originalAffineRefinedNativePuncture_affine Γ(U.left, ⊤)
      (originalCylinderNativeIso U T e)
      (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
      (originalCylinderNativeIso_projection U T e) B a.left
  have H₀ := Scheme.originalAffineRefinedNativeMarked_isPullback
    Γ(U.left, ⊤) (originalCylinderNativeIso U T e)
    (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
    (originalCylinderNativeIso_projection U T e) B p.left W hW z t H
  have hs : t ≫ p0 = z₀ := by simpa only [Category.id_comp] using H₀.w
  have hz₀ : Set.range z₀ = (Set.range a0)ᶜ :=
    Scheme.originalAffineRefinedNative_complement Γ(U.left, ⊤)
      (originalCylinderNativeIso U T e)
      (Motivic.PresheafWithTransfers.originalRepresentativeCoefficientMap U T e)
      (originalCylinderNativeIso_projection U T e) B a.left z hz
  let : Etale (nativeOriginalRefinedPunctureArrow U T e A a B O V).left :=
    nativeOriginalRefinedPunctureArrow_etale U T e A a B O V
  let : Etale (nativeOriginalRefinedSourceArrow U T e Y p B W hW O V).left :=
    nativeOriginalRefinedSourceArrow_etale U T e Y p B W hW O V
  apply ofTwoArrows_mem_nisnevichTopology_of_field_lifting
  intro K _ x
  obtain ⟨b, hb⟩ | ⟨c, hc⟩ := nativeCoefficientCover_field_lifting
    Γ(B.toScheme, ⊤) O V p0 a0 z₀ t hs hz₀
      (x ≫ eS.inv)
  · left
    refine ⟨b, ?_⟩
    have hl := lift_comp_iso_eq b a2 x eS hb
    have he := congrArg (fun m => b ≫ m)
      (nativeOriginalRefinedPunctureArrow_left U T e A a B O V)
    exact he.trans hl
  · right
    refine ⟨c, ?_⟩
    have hl := lift_comp_iso_eq c p2 x eS hc
    have he := congrArg (fun m => c ≫ m)
      (nativeOriginalRefinedSourceArrow_left U T e Y p B W hW O V)
    exact he.trans hl

end AlgebraicGeometry.Scheme.SmoothSite
