/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.OriginalHistoryLifting
public import Motivic.Transfers.Presheaf.Sheafification.Representatives.SectionChosen
public import Motivic.Cohomology.A1.Sheafification.CylinderCriterion

/-! # Original whole-cylinder lifting

For `k : Type u`, `[Field k]` and an HI
`P : PresheafWithTransfers.{u + 1} k`,
`modelWholeCylinderLifting_of_isA1Invariant` constructs `ModelWholeCylinderLifting P`.
It uses the original section-chosen representatives and one normalization and
section history.

For each integral affine smooth source, the output retains a nonempty original
base open and an image section on its whole affine-line cylinder, with the
actual sheafification-unit equation. The lifting datum is a conclusion from
these coefficient inputs.
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

namespace Motivic.PresheafWithTransfers

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

/-- Construct the original whole-cylinder lifting datum
from an original HI presheaf, without HI of its sheafification or image gluing. -/
theorem modelWholeCylinderLifting_of_isA1Invariant
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ModelWholeCylinderLifting P := by
  classical
  intro X _ _ g
  obtain ⟨U, jU, hjU, hUn, hUa, T, eT, A, Y, a, p, hAa, ha,
      hp, hcover, Z, z, hzc, hfin, hcomp, hYZ, Borig, bAorig, bYorig, HB,
      sA, sY, hm, hgA, hgY, r₀, hr₀, W, hWa, hW, s₀, hs₀, _H₀,
      haffOverlap, hgW, hmW, Hchoice⟩ :=
    exists_sectionChosen_distinguished_nisnevichImage_representatives P X g
  let : IsAffine U.left := hUa
  let : Nonempty U.left := hUn
  let : IsOpenImmersion jU.left := hjU
  let : IsIntegral U.left := isIntegral_of_isOpenImmersion jU.left
  let : IsAffine A.left := hAa
  let : IsOpenImmersion a.left := ha
  let : Etale p.left := hp
  let : IsClosedImmersion z := hzc
  let : IsIso (pullback.snd p.left z) := hYZ
  let : IsAffine W.toScheme := hWa
  let B₀ : (Spec Γ(U.left, ⊤)).Opens := PrimeSpectrum.basicOpen r₀
  let : IsAffine B₀.toScheme := IsAffineOpen.Spec_basicOpen r₀
  let R₀ := Γ(B₀.toScheme, ⊤)
  let q₀ := originalRepresentativeCoefficientMap U T eT
  let eN := originalCylinderNativeIso U T eT
  let heN := originalCylinderNativeIso_projection U T eT
  let p₀ := Scheme.originalAffineRefinedNativeMap Γ(U.left, ⊤) eN q₀ heN
    B₀ p.left W hW
  let a₀ := Scheme.originalAffineRefinedNativePuncture Γ(U.left, ⊤) eN q₀ heN B₀ a.left
  let z₀ := Scheme.originalAffineRefinedNativeMarked Γ(U.left, ⊤) eN q₀ heN B₀ z
  let : IsAffine ((a.left ≫ q₀) ⁻¹ᵁ B₀).toScheme :=
    Scheme.originalAffineRefinedNativePuncture_affine Γ(U.left, ⊤) eN q₀ heN B₀ a.left
  obtain ⟨hd₀, hn₀, hno₀, hp₀, hqc₀, hsep₀, hzc₀, hzf₀, hsN, HN, Hnorm⟩ := Hchoice
  let := hd₀
  let := hn₀
  let := hno₀
  let := hp₀
  let := hqc₀
  let := hsep₀
  let := hzc₀
  let := hzf₀
  -- Finite over the coefficient base makes the original marked chart proper.
  -- Closedness follows from its original closed immersion and the open chart.
  let : IsProper ((z₀ ≫ chart R₀ 0) ≫
      ProjectiveSpace.toSpec R₀ (ULift.{u} (Fin 2))) := by
    rw [Category.assoc, chart_toSpec]
    infer_instance
  let : IsProper (z₀ ≫ chart R₀ 0) :=
    IsProper.of_comp _ (ProjectiveSpace.toSpec R₀ (ULift.{u} (Fin 2)))
  let : IsClosedImmersion (z₀ ≫ chart R₀ 0) :=
    IsClosedImmersion.of_isPreimmersion _ (z₀ ≫ chart R₀ 0).isClosedMap.isClosed_range
  obtain ⟨r₁, hr₁, hfree₀, O, hO, hηO, hOr, D₁, d₁, hdc₁, hdr₁,
      hdj₁, hds₁, hdf₁, bOld, bE₁, bI₁, hbOld, hbE₁, hbI₁, x, Hcommon⟩ := Hnorm
  let : IsAffine O.toScheme := hO
  obtain ⟨V, hV, hxV, hVtop, hq₁, hs₁, Hsource, Htarget⟩ := Hcommon
  let : IsAffine V.toScheme := hV
  let Hist := OriginalHistorySiteLifting.originalHistory
    (U := U) (Tc := T) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
    (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
    (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
    (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
    (V := V) (hq₁ := hq₁) (hs₁ := hs₁)
  let Bounds : Hist.BoundaryWitnesses :=
    { hηO := hηO
      x := x
      hxV := hxV
      r := r₁
      hOr := hOr
      hfree₀ := hfree₀
      D := D₁
      d := d₁
      closedD := hdc₁
      hdr := hdr₁
      finiteD := hdf₁
      bI := bI₁
      hbI := hbI₁
      bE := bE₁
      hbE := hbE₁ }
  have sourceTuple := Hist.nonempty_sourceWitnesses Bounds Hsource
  obtain ⟨Wsrc⟩ := sourceTuple
  have targetTuple := Hist.nonemptyTargetWitnesses Htarget
  obtain ⟨Tsec⟩ := targetTuple
  refine ⟨SmoothSite.nativeOriginalBaseSite U B₀ O V,
    SmoothSite.nativeOriginalBaseInclusion U B₀ O V ≫ jU, ?_⟩
  exact NativeOwnedOriginalHistorySiteLifting.wholeCylinder_lift
    (U := U) (Tc := T) (eT := eT) (A := A) (Y := Y) (a := a) (p := p)
    (z := z) (B₀ := B₀) (W := W) (hW := hW) (s₀ := s₀) (hcomp := hcomp)
    (hd₀ := hd₀) (hn₀ := hn₀) (hno₀ := hno₀) (hp₀ := hp₀) (hqc₀ := hqc₀)
    (hsep₀ := hsep₀) (hzc₀ := hzc₀) (hzf₀ := hzf₀) (hsN := hsN) (HN := HN) (O := O)
    (V := V) (hq₁ := hq₁) (hs₁ := hs₁)
    Bounds Wsrc Tsec P hP jU bAorig bYorig HB g sA sY hm hgA hgY

end Motivic.PresheafWithTransfers
