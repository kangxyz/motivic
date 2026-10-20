/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationHistory
public import Motivic.Transfers.Presheaf.Sheafification.Representatives.SectionChosen
public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.NativeOriginalRefinedCover

/-! # Canonical history of original representatives

Over a field, package the original affine coefficient and source refinements into the
existing `OriginalLocalizationSeed` and `OriginalLocalizationHistory` records.
The same etale source, puncture, whole finite marked scheme, marked lift and
chosen affine coefficient opens are stored as data.

The normal Noetherian coefficient domain, etale/separated/quasi-compact map,
finite marked map, marked pullback square and projection equations remain explicit.
`originalHistorySeed` fixes the first stage; `originalHistory` adds the supplied
final affine open without selecting replacement representatives or sections.
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

namespace Motivic.PresheafWithTransfers.OriginalHistorySiteLifting
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

/-- The original refined geometry, stored once in the existing seed record. -/
def originalHistorySeed : OriginalLocalizationSeed.{u} where
  R := ((B₀.toScheme.presheaf.obj (Opposite.op ⊤)))
  commRing := inferInstance
  domain := hd₀
  normal := hn₀
  noetherian := hno₀
  Y := W.toScheme
  A := ((a.left ≫ (originalRepresentativeCoefficientMap U Tc eT)) ⁻¹ᵁ B₀).toScheme
  Z := ((z ≫ (originalRepresentativeCoefficientMap U Tc eT)) ⁻¹ᵁ B₀).toScheme
  affineY := inferInstance
  affineA := Scheme.originalAffineRefinedNativePuncture_affine
    Γ(U.left, ⊤) (originalCylinderNativeIso U Tc eT) (originalRepresentativeCoefficientMap U Tc
      eT) (originalCylinderNativeIso_projection U Tc eT) B₀ a.left
  p := (Scheme.originalAffineRefinedNativeMap
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ p.left W hW)
  etaleP := hp₀
  quasiCompactP := hqc₀
  separatedP := hsep₀
  a := (Scheme.originalAffineRefinedNativePuncture
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ a.left)
  openA := inferInstance
  z := (Scheme.originalAffineRefinedNativeMarked
  (U.left.presheaf.obj (Opposite.op ⊤)) (originalCylinderNativeIso U Tc eT)
      (originalRepresentativeCoefficientMap U Tc eT) (originalCylinderNativeIso_projection U Tc
      eT) B₀ z)
  closedZ := hzc₀
  finiteZ := hzf₀
  s := s₀
  hs := hsN
  H := HN
  hz := Scheme.originalAffineRefinedNative_complement
    Γ(U.left, ⊤) (originalCylinderNativeIso U Tc eT) (originalRepresentativeCoefficientMap U Tc
      eT) (originalCylinderNativeIso_projection U Tc eT) B₀ a.left z hcomp
  O := O
  affineO := inferInstance


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

/-- The same common second open and its original equations. -/
def originalHistory : OriginalLocalizationHistory.{u} where
  seed := (originalHistorySeed
  (U := U) (Tc := Tc) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
  (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
  (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
  (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O))
  V := V
  affineV := inferInstance
  hq₁ := hq₁
  hs₁ := hs₁


end Motivic.PresheafWithTransfers.OriginalHistorySiteLifting
