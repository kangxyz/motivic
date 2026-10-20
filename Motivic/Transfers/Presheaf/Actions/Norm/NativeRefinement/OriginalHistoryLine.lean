/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.OriginalHistory
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalCylinder

/-! # The original history coefficient line

Over a field, for the fixed history and its boundary, source and target witnesses,
`ownedLineIso` identifies the native middle-input line with
`nativeOriginalLineSite` over the final coefficient base. The source-map
comparison keeps the same original history map.

`ownedCylinderIso` uses the original cylinder isomorphism, and
`ownedLineRestriction` gives the one line-to-original-target map used by both
restriction diagrams. Their displayed equations retain the original affine
base restrictions and fixed witnesses.
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

namespace Motivic.PresheafWithTransfers.OriginalHistoryEndpointEqualities
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

omit [Etale p.left] in
/-- Canonical equality of the original and stored endpoints, with unchanged maps. -/
theorem ownedLineSite_eq :
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  N.nativeLineSite = SmoothSite.nativeOriginalLineSite U B₀ O V := by
  intro N
  rfl

omit [Etale p.left] in
/-- The stored map is the same history map without specializing a free field-map API. -/
theorem native_p_eq_history :
  let H := originalHistory
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁)
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  N.p = H.p₂ := by
  intro H N
  rfl

end Motivic.PresheafWithTransfers.OriginalHistoryEndpointEqualities

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativeLine
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

/-- The same proved comparison with the original line, shared by all later maps. -/
def ownedLineIso :
    (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).toInput.siteX ≅
      SmoothSite.nativeOriginalLineSite U B₀ O V := by
  exact (Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)).nativeLineSiteIso
    ≪≫
    eqToIso (OriginalHistoryEndpointEqualities.ownedLineSite_eq
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)

/-- The chosen cylinder comparison uses the original cylinder isomorphism. -/
def ownedCylinderIso :=
  (ownedLineIso
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec) ≪≫
    SmoothSite.nativeOriginalCylinderIso U Tc eT B₀ O V

/-- One line-to-original-target map is shared by both restriction squares. -/
def ownedLineRestriction :=
  (ownedLineIso
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec).hom ≫
    SmoothSite.nativeOriginalLineRestriction U Tc eT B₀ O V

omit [Etale p.left] in
/-- The original whole-cylinder map agrees with the one shared line restriction. -/
theorem ownedCylinderIso_comp :
    (ownedCylinderIso
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec).hom ≫
      SmoothSite.nativeOriginalWholeCylinderMap U Tc eT B₀ O V =
    ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec := by
  change ((ownedLineIso
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec).hom ≫
    (SmoothSite.nativeOriginalCylinderIso U Tc eT B₀ O V).hom) ≫
    ((SmoothSite.nativeOriginalCylinderIso U Tc eT B₀ O V).inv ≫
      SmoothSite.nativeOriginalLineRestriction U Tc eT B₀ O V) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

omit [Etale p.left] in
/-- The actual ancestry coefficient chain is the shared original line restriction. -/
theorem ancestryLineRestriction_eq :
  let D := Wsrc.toNativeAncestry Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  D.lineToSeed ≫ nativeAffineLineRestriction Γ(U.left, ⊤) B₀.ι ≫
      (originalCylinderNativeIso U Tc eT).inv =
    (ownedLineRestriction
    (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
    (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
    (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
    (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec).left := by
  intro D
  let N := Wsrc.toNative Tsec (SmoothSite.nativeOriginalFinalFieldMap U B₀ O V)
  let hline := (OriginalHistoryEndpointEqualities.ownedLineSite_eq
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p) (z := z) (B₀ := B₀)
  (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp) (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀)
  (hp₀ := hp₀) (hqc₀ := hqc₀) (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN)
  (HN := HN) (O := O) (V := V) (hq₁ := hq₁) (hs₁ := hs₁) Bounds Wsrc Tsec)
  change _ = (N.nativeLineSiteIso ≪≫ eqToIso hline).hom.left ≫
    (SmoothSite.nativeOriginalLineRestriction U Tc eT B₀ O V).left
  rw [N.nativeLineSiteIso_transport_hom_left hline]
  let τV := nativeAffineLineRestriction Γ(O.toScheme, ⊤) V.ι
  let τO := nativeAffineLineRestriction Γ(B₀.toScheme, ⊤) O.ι
  let τB := nativeAffineLineRestriction Γ(U.left, ⊤) B₀.ι
  let eN := originalCylinderNativeIso U Tc eT
  change (τV ≫ τO) ≫ τB ≫ eN.inv = (𝟙 _) ≫ ((τV ≫ τO ≫ τB) ≫ eN.inv)
  simp only [Category.id_comp, Category.assoc]

end Motivic.PresheafWithTransfers.OriginalHistoryNativeLine
