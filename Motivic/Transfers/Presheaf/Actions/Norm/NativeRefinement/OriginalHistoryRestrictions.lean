/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.OriginalHistoryLine
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.NativeOriginalRefinedSource

/-! # Original-history restriction assembly

Over a field, construct the original source and puncture scheme restrictions from the
ancestry maps of one fixed history. Their commutation with the same
`ownedLineRestriction` equips them with the actual native smooth-site
morphisms `sourceRestriction` and `punctureRestriction`.

The resulting `transport` satisfies the five literal compatibility laws used
by the lifting adapter. The original affine coefficient opens, full marked
data and boundary/source/target witnesses remain fixed throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
open RelativeProjectiveLine AlgebraicGeometry.FiniteSchemeNormBaseChange
open Motivic Motivic.PresheafWithTransfers
universe u v w
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativeRestrictions
open OriginalHistorySiteLifting

-- These are caller-local instances, not assumed exports of a native action leaf.
local instance sharedInputSmoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1
      (chart R 0 ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [chart_toSpec]
  infer_instance


variable {k : Type u} [Field k]
  (U Tc : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (eT : Tc ≅ SmoothSite.a1Cylinder (.of k) U)
  (A Y : SmoothSite (Spec (.of k))) [IsAffine A.left]
  (a : A ⟶ Tc) [IsOpenImmersion a.left] (p : Y ⟶ Tc) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Tc.left)
  (B₀ : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B₀.toScheme]
  (W : Y.left.Opens) [IsAffine W.toScheme]


variable (hW : W ≤ p.left ⁻¹ᵁ ((originalRepresentativeCoefficientMap U Tc eT) ⁻¹ᵁ B₀))


variable (s₀ : ((z ≫ (originalRepresentativeCoefficientMap U Tc eT)) ⁻¹ᵁ B₀).toScheme ⟶ W.toScheme)
  (hcomp : Set.range z = (Set.range a.left)ᶜ)
  (hd₀ : IsDomain ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hn₀ : IsIntegrallyClosed
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hno₀ : IsNoetherianRing
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))
  (hp₀ : Etale (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hqc₀ : QuasiCompact (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hsep₀ : IsSeparated (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW))
  (hzc₀ : IsClosedImmersion (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (hzf₀ : IsFinite ((Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z) ≫ boundaryLineProjection ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))))
  (hsN : s₀ ≫ (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) = (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (HN : IsPullback s₀ (𝟙 _) (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z))
  (O : (Spec (.of ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))).Opens) [IsAffine O.toScheme]

variable (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  (hq₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).j₁ ≫
      (((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).F₁ ≫
      ProjectiveSpace.toSpec ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁ (ULift.{u}
      (Fin 2))) =
    ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ ≫
      boundaryLineProjection ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁)
  (hs₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).s₁ ≫
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ =
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).z₁)

variable (Bounds : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p
      := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).BoundaryWitnesses)
  (Wsrc : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).SourceWitnesses Bounds)
  (Tsec : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).TargetWitnesses)

/-- The unchanged three open inclusions, starting at the owned native source. -/
def sourceRestrictionScheme :
    (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).Y ⟶ Y.left :=
  (Wsrc.toNativeAncestry Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).sourceToSeed ≫ W.ι

omit [Etale p.left] in
/-- The original source representative is restricted along the shared coefficient line. -/
theorem sourceRestrictionScheme_square :
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  (sourceRestrictionScheme
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) ≫ p.left =
    N.p ≫ (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec).left := by
  intro N
  let D := Wsrc.toNativeAncestry Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  let τB := nativeAffineLineRestriction Γ(U.left, ⊤) B₀.ι
  let eN := originalCylinderNativeIso U Tc eT
  have hB : D.seedP ≫ τB = W.ι ≫ p.left ≫ eN.hom :=
    Scheme.originalAffineRefinedNativeMap_coordinate Γ(U.left, ⊤) eN
      (originalRepresentativeCoefficientMap U Tc eT)
      (originalCylinderNativeIso_projection U Tc eT) B₀ p.left W hW
  have hcat := SmoothSite.threeRestrictionSquares N.p D.seedP D.seedP p.left
    D.sourceToSeed (𝟙 _) W.ι D.lineToSeed (𝟙 _) τB eN (Iso.refl _)
    D.sourceSquare (by simp only [Category.comp_id, Category.id_comp]) hB
  have hs : (D.sourceToSeed ≫ W.ι) ≫ p.left =
      N.p ≫ (D.lineToSeed ≫ τB ≫ eN.inv) := by
    simpa only [Category.assoc, Category.id_comp, Category.comp_id,
      Iso.refl_hom, Iso.refl_inv] using hcat
  exact hs.trans (congrArg (fun f => N.p ≫ f)
    (OriginalHistoryNativeLine.ancestryLineRestriction_eq
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec))

end Motivic.PresheafWithTransfers.OriginalHistoryNativeRestrictions

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativePunctureRestrictions
open OriginalHistorySiteLifting

-- These are caller-local instances, not assumed exports of a native action leaf.
local instance sharedInputSmoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1
      (chart R 0 ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [chart_toSpec]
  infer_instance


variable {k : Type u} [Field k]
  (U Tc : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (eT : Tc ≅ SmoothSite.a1Cylinder (.of k) U)
  (A Y : SmoothSite (Spec (.of k))) [IsAffine A.left]
  (a : A ⟶ Tc) [IsOpenImmersion a.left] (p : Y ⟶ Tc) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Tc.left)
  (B₀ : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B₀.toScheme]
  (W : Y.left.Opens) [IsAffine W.toScheme]


variable (hW : W ≤ p.left ⁻¹ᵁ ((originalRepresentativeCoefficientMap U Tc eT) ⁻¹ᵁ B₀))


variable (s₀ : ((z ≫ (originalRepresentativeCoefficientMap U Tc eT)) ⁻¹ᵁ B₀).toScheme ⟶ W.toScheme)
  (hcomp : Set.range z = (Set.range a.left)ᶜ)
  (hd₀ : IsDomain ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hn₀ : IsIntegrallyClosed
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hno₀ : IsNoetherianRing
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))
  (hp₀ : Etale (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hqc₀ : QuasiCompact (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hsep₀ : IsSeparated (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW))
  (hzc₀ : IsClosedImmersion (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (hzf₀ : IsFinite ((Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z) ≫ boundaryLineProjection ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))))
  (hsN : s₀ ≫ (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) = (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (HN : IsPullback s₀ (𝟙 _) (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z))
  (O : (Spec (.of ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))).Opens) [IsAffine O.toScheme]

variable (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  (hq₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).j₁ ≫
      (((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).F₁ ≫
      ProjectiveSpace.toSpec ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁ (ULift.{u}
      (Fin 2))) =
    ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ ≫
      boundaryLineProjection ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁)
  (hs₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).s₁ ≫
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ =
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).z₁)

variable (Bounds : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p
      := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).BoundaryWitnesses)
  (Wsrc : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).SourceWitnesses Bounds)
  (Tsec : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).TargetWitnesses)

/-- The unchanged three open inclusions, starting at the owned native puncture. -/
def punctureRestrictionScheme :
    (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).A ⟶ A.left :=
  (Wsrc.toNativeAncestry Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).punctureToSeed ≫
    ((a.left ≫ originalRepresentativeCoefficientMap U Tc eT) ⁻¹ᵁ B₀).ι

omit [Etale p.left] in
/-- The original puncture representative is restricted along the shared coefficient line. -/
theorem punctureRestrictionScheme_square :
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  (punctureRestrictionScheme
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) ≫ a.left =
    N.a ≫ (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec).left := by
  intro N
  let D := Wsrc.toNativeAncestry Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  let τB := nativeAffineLineRestriction Γ(U.left, ⊤) B₀.ι
  let eN := originalCylinderNativeIso U Tc eT
  let q := originalRepresentativeCoefficientMap U Tc eT
  let i₀ := ((a.left ≫ q) ⁻¹ᵁ B₀).ι
  have hB : D.seedAmap ≫ τB = i₀ ≫ a.left ≫ eN.hom := by
    have hc : (Scheme.originalAffineRefinedTargetIso Γ(U.left, ⊤) eN q
        (originalCylinderNativeIso_projection U Tc eT) B₀).hom ≫ τB =
        (q ⁻¹ᵁ B₀).ι ≫ eN.hom :=
      Scheme.originalAffineRefinedTargetIso_coordinate Γ(U.left, ⊤) eN q
        (originalCylinderNativeIso_projection U Tc eT) B₀
    have hr := morphismRestrict_ι a.left (q ⁻¹ᵁ B₀)
    exact (Category.assoc (a.left ∣_ (q ⁻¹ᵁ B₀))
      (Scheme.originalAffineRefinedTargetIso Γ(U.left, ⊤) eN q
        (originalCylinderNativeIso_projection U Tc eT) B₀).hom τB).trans
      ((congrArg (fun m => (a.left ∣_ (q ⁻¹ᵁ B₀)) ≫ m) hc).trans
        ((Category.assoc (a.left ∣_ (q ⁻¹ᵁ B₀)) (q ⁻¹ᵁ B₀).ι eN.hom).symm.trans
          ((congrArg (fun m => m ≫ eN.hom) hr).trans
            (Category.assoc i₀ a.left eN.hom))))
  have hcat := SmoothSite.threeRestrictionSquares N.a D.seedAmap D.seedAmap a.left
    D.punctureToSeed (𝟙 _) i₀ D.lineToSeed (𝟙 _) τB eN (Iso.refl _)
    D.punctureSquare (by simp only [Category.comp_id, Category.id_comp]) hB
  have hs : (D.punctureToSeed ≫ i₀) ≫ a.left =
      N.a ≫ (D.lineToSeed ≫ τB ≫ eN.inv) := by
    simpa only [Category.assoc, Category.id_comp, Category.comp_id,
      Iso.refl_hom, Iso.refl_inv] using hcat
  exact hs.trans (congrArg (fun f => N.a ≫ f)
    (OriginalHistoryNativeLine.ancestryLineRestriction_eq
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec))

end Motivic.PresheafWithTransfers.OriginalHistoryNativePunctureRestrictions

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativeSiteAssembly
open OriginalHistorySiteLifting

-- These are caller-local instances, not assumed exports of a native action leaf.
local instance sharedInputSmoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1
      (chart R 0 ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [chart_toSpec]
  infer_instance


variable {k : Type u} [Field k]
  (U Tc : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (eT : Tc ≅ SmoothSite.a1Cylinder (.of k) U)
  (A Y : SmoothSite (Spec (.of k))) [IsAffine A.left]
  (a : A ⟶ Tc) [IsOpenImmersion a.left] (p : Y ⟶ Tc) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Tc.left)
  (B₀ : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B₀.toScheme]
  (W : Y.left.Opens) [IsAffine W.toScheme]


variable (hW : W ≤ p.left ⁻¹ᵁ ((originalRepresentativeCoefficientMap U Tc eT) ⁻¹ᵁ B₀))


variable (s₀ : ((z ≫ (originalRepresentativeCoefficientMap U Tc eT)) ⁻¹ᵁ B₀).toScheme ⟶ W.toScheme)
  (hcomp : Set.range z = (Set.range a.left)ᶜ)
  (hd₀ : IsDomain ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hn₀ : IsIntegrallyClosed
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))) (hno₀ : IsNoetherianRing
      ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))
  (hp₀ : Etale (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hqc₀ : QuasiCompact (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)) (hsep₀ : IsSeparated (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW))
  (hzc₀ : IsClosedImmersion (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (hzf₀ : IsFinite ((Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z) ≫ boundaryLineProjection ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))))
  (hsN : s₀ ≫ (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) = (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)) (HN : IsPullback s₀ (𝟙 _) (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW) (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z))
  (O : (Spec (.of ((B₀.toScheme.presheaf.obj (Opposite.op ⊤))))).Opens) [IsAffine O.toScheme]

variable (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  (hq₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).j₁ ≫
      (((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).F₁ ≫
      ProjectiveSpace.toSpec ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁ (ULift.{u}
      (Fin 2))) =
    ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ ≫
      boundaryLineProjection ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).R₁)
  (hs₁ : ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).s₁ ≫
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).p₁ =
      ((originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))).z₁)

variable (Bounds : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p
      := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).BoundaryWitnesses)
  (Wsrc : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).SourceWitnesses Bounds)
  (Tsec : (originalHistory (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
  (V := V) (hq₁ := hq₁) (hs₁ := hs₁)).TargetWitnesses)

/-- The original source restriction, with its genuine native site structure. -/
def sourceRestriction : (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O
      V)).toInput.siteY ⟶ Y :=
  (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).sourceRestrictionOfSquare p
    (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme_square
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)

omit [Etale p.left] in
/-- The source restriction square uses the one shared original line map. -/
theorem sourceRestriction_comp :
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  (sourceRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) ≫ p = N.toInput.pSite
      ≫ (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) := by
  intro N
  exact N.sourceRestrictionOfSquare_comp p (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme_square
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)

/-- The original puncture restriction, with its genuine native site structure. -/
def punctureRestriction : (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O
      V)).toInput.siteA ⟶ A :=
  (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O
      V)).punctureRestrictionOfSquare a
    (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme_square
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)

omit [Etale p.left] in
/-- The puncture restriction square uses the one shared original line map. -/
theorem punctureRestriction_comp :
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  (punctureRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) ≫ a = N.aSite ≫
      (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) := by
  intro N
  exact N.punctureRestrictionOfSquare_comp a (OriginalHistoryNativeLine.ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme_square
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)

/-- The existing five-map transport on the actual native source and puncture. -/
def transport :=
  (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).nativeTransport
    (OriginalHistoryNativeLine.ownedCylinderIso
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) (punctureRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) (sourceRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)

omit [Etale p.left] in
/-- All five actual transport laws follow from the proved original restriction squares. -/
theorem transport_compatible :
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  let e := (OriginalHistoryNativeLine.ownedCylinderIso
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  (transport
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec).Compatible a p
      (N.aSite ≫ e.hom) (N.toInput.pSite ≫ e.hom)
    (punctureRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) (sourceRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) := by
  intro N e
  exact N.nativeTransport_compatible a p (OriginalHistoryNativeLine.ownedLineRestriction
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) e (punctureRestriction
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) (sourceRestriction
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
    (punctureRestriction_comp
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) (sourceRestriction_comp
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)

end Motivic.PresheafWithTransfers.OriginalHistoryNativeSiteAssembly
