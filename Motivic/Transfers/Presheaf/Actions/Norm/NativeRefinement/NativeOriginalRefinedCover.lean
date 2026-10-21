/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.OriginalNativeCover
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
  let sourceMap := originalAffineRefinedSourceMap Γ(U.left, ⊤) eN q heN B p.left W hW O V
  let punctureMap := originalAffineRefinedPunctureMap Γ(U.left, ⊤) eN q heN B a.left O V
  let u := punctureMap ≫ (nativeOriginalLineSite U B O V).hom
  let v := sourceMap ≫ (nativeOriginalLineSite U B O V).hom
  let α := nativeOriginalRefinedPunctureArrow U T e A a B O V
  let β := nativeOriginalRefinedSourceArrow U T e Y p B W hW O V
  exact @originalAffineRefinedCover_mem_nisnevichTopology k inferInstance Γ(U.left, ⊤)
    T.left A.left Y.left eN q heN a.left inferInstance p.left B inferInstance W hW
    O inferInstance V inferInstance u
    (nativeOriginalRefinedPunctureSite U T e A a B O V).prop.1.1
    (nativeOriginalRefinedPunctureSite U T e A a B O V).prop.1.2
    (nativeOriginalRefinedPunctureSite U T e A a B O V).prop.2 v
    (nativeOriginalRefinedSourceSite U T e Y p B W hW O V).prop.1.1
    (nativeOriginalRefinedSourceSite U T e Y p B W hW O V).prop.1.2
    (nativeOriginalRefinedSourceSite U T e Y p B W hW O V).prop.2
    (a1Cylinder (.of k) (nativeOriginalBaseSite U B O V)) α
    (nativeOriginalRefinedPunctureArrow_etale U T e A a B O V) β
    (nativeOriginalRefinedSourceArrow_etale U T e Y p B W hW O V)
    ((forgetScheme (Spec (.of k))).mapIso (nativeOriginalCylinderIso U T e B O V))
    (nativeOriginalRefinedPunctureArrow_left U T e A a B O V)
    (nativeOriginalRefinedSourceArrow_left U T e Y p B W hW O V)
    Z z inferInstance hz t H

end AlgebraicGeometry.Scheme.SmoothSite
