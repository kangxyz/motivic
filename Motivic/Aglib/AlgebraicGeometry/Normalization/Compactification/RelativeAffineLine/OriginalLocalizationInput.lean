/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeOriginalMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationHistory
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.AffineSpecSquare

/-! # Native input of the original localization history

The original source and target witnesses construct one native middle input.
Its ancestry retains the same two actual opens, original source and puncture
maps, and one common coefficient-line restriction. Current consumers are the
original-history lifting and its actual restriction assembly.

Intended upstream module:
Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationInput

The exact hypotheses are the record fields and declaration signatures below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible RelativeProjectiveLine
open Scheme.RelativeCurvePencil
universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
attribute [local instance] OriginalLocalizationSeed.commRing OriginalLocalizationSeed.domain
  OriginalLocalizationSeed.normal OriginalLocalizationSeed.noetherian
  OriginalLocalizationSeed.affineY OriginalLocalizationSeed.affineA
  OriginalLocalizationSeed.etaleP OriginalLocalizationSeed.quasiCompactP
  OriginalLocalizationSeed.separatedP OriginalLocalizationSeed.openA
  OriginalLocalizationSeed.closedZ OriginalLocalizationSeed.finiteZ
  OriginalLocalizationSeed.affineO OriginalLocalizationHistory.affineV
  OriginalTargetSectionWitnesses.unitA OriginalTargetSectionWitnesses.unitB
namespace OriginalLocalizationHistory
attribute [local instance] chartOpen chartSmooth seedEtale seedOpen seedInclusionOpen
  seedMarkedFinite seedMarkedClosed sourceEtale punctureOpen inclusionOpen sourceSmooth
  lineSmooth lineSeparated compactificationProper retainedProductOpen seedProjectiveMarked
  firstProjectiveMarked finalProjectiveMarked firstSourceAffine firstPunctureAffine
  finalSourceAffine finalPunctureAffine retainedAffine overlapAffine retainedOpen
  overlapSmooth overlapFlat infinityAffine
local instance (S : OriginalLocalizationSeed.{u}) : IsFinite S.F₁ :=
  boundaryBaseProjectiveMap_finite S.R (ULift.{u} (Fin 2)) (toProjectiveLine S.R S.p) S.O
local instance (H : OriginalLocalizationHistory.{u}) : IsFinite H.F₂ :=
  boundaryBaseProjectiveMap_finite H.seed.R₁ (ULift.{u} (Fin 2)) H.seed.F₁ H.V

namespace SourceWitnesses
attribute [local instance] OriginalTargetSectionWitnesses.unitA OriginalTargetSectionWitnesses.unitB
variable {H : OriginalLocalizationHistory.{u}} {B : H.BoundaryWitnesses}
  {k : Type u} [Field k] (W : H.SourceWitnesses B) (T : H.TargetWitnesses)
  (t : Spec Γ(H.V.toScheme, ⊤) ⟶ Spec (.of k)) [Smooth t]


/-- Assemble the same native input once, using only internally derived geometry. -/
def toNative :
    AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
      k := by
  have props := (B.ringProperties₂)
  let := (props.1)
  let := (props.2.1)
  let := (props.2.2)
  exact ({
    R := ((Γ(H.V.toScheme, ⊤)).carrier)
    Y := (finalOriginalSource H.seed.R H.seed.p H.seed.O H.V)
    commRing := (Γ(H.V.toScheme, ⊤)).commRing
    domain := props.1
    integrallyClosed := props.2.1
    noetherian := props.2.2
    A := (boundaryBaseCoverOpen (boundaryLineProjection H.seed.R₁) H.seed.a₁ ⊤ H.V).toScheme
    Z := ((H.seed.z₁ ≫ boundaryLineProjection H.seed.R₁) ⁻¹ᵁ H.V).toScheme
    C := boundaryBaseCompactification
      (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2))) H.V
    D := ((B.d ≫ (H.seed.F₁ ≫
      ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))) ⁻¹ᵁ H.V).toScheme
    V := (((pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) ≫
      (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))) ⁻¹ᵁ H.V).toScheme
    WA := retainedProduct (H.jA₂ ≫ H.π₂) H.π₂
      (targetNativeRetained H.seed.R₁ H.V (H.seed.a₁ ≫ chart H.seed.R₁ 0))
    DA := ((H.dA₁ ≫ ((𝟙 _) ≫
      ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))) ⁻¹ᵁ H.V).toScheme
    B := boundaryBaseOverlap (boundaryLineProjection H.seed.R₁)
      H.seed.p₁ H.seed.a₁ ⊤ H.V
    affineY := inferInstanceAs (IsAffine H.Y₂)
    affineA := inferInstanceAs (IsAffine
      (boundaryBaseCoverOpen (boundaryLineProjection H.seed.R₁) H.seed.a₁ ⊤ H.V).toScheme)
    affineV := inferInstanceAs (IsAffine
      (((pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) ≫
        (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))) ⁻¹ᵁ H.V).toScheme)
    affineB := inferInstanceAs (IsAffine
      (boundaryBaseOverlap (boundaryLineProjection H.seed.R₁) H.seed.p₁ H.seed.a₁ ⊤ H.V))
    finiteF := inferInstanceAs (IsFinite H.F₂)
    openJ := inferInstanceAs (IsOpenImmersion H.j₂)
    smoothJ := inferInstanceAs (SmoothOfRelativeDimension 1 (H.j₂ ≫ (H.F₂ ≫ H.π₂)))
    flatP := inferInstanceAs (Flat H.p₂)
    openA := inferInstanceAs (IsOpenImmersion H.a₂)
    closedZChart := inferInstanceAs (IsClosedImmersion (H.z₂ ≫ H.jA₂))
    openVB := inferInstanceAs (IsOpenImmersion H.vB)
    affineDA := inferInstanceAs (IsAffineHom H.dA₂)
    openIA := inferInstanceAs (IsOpenImmersion H.iA)
    smoothAlpha := inferInstanceAs (Smooth H.αorig)
    flatBeta := inferInstanceAs (Flat H.βorig)
    smoothT := inferInstanceAs (Smooth t)
    F := (H.F₂)
    j := (H.j₂)
    p := (H.p₂)
    hq := (W.hqn)
    hret := (H.hret₂)
    a := (H.a₂)
    z := (H.z₂)
    s := (H.s₂)
    hs := (H.hs₂)
    H := (H.markedSquare)
    hsK := (H.hsK₂)
    e := (H.e₂)
    ha := (W.han)
    d := (B.d₂)
    hd := (W.hdn)
    source := (W.source)
    vB := (H.vB)
    vA := (H.vA)
    hsmall := (H.hsmall)
    hcover := (B.hc₂)
    dA := (H.dA₂)
    hdA := (H.hdA₂)
    bI := (B.bI₂)
    hbI := (B.hbI₂)
    bE := (B.bE₂)
    hbE := (B.hbE₂)
    iA := (H.iA)
    target := (T)
    αorig := (H.αorig)
    βorig := (H.βorig)
    horig := (H.horig)
    φorig := (H.φorig)
    hφorig := (H.hφorig)
    hcoverA := (H.hcoverA)
    t := (t)
    hpuncture := (H.hpuncture)
    hfree := (B.hfree₂) })


end SourceWitnesses

end OriginalLocalizationHistory
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
attribute [local instance] commRing
variable {k : Type u} [Field k]

/-- The original two localization restrictions, owned by the same native input. -/
structure NativeAncestry (N : NativeOriginalMiddleInput k) where
  /-- The original source before the two retained localizations. -/
  seedY : Scheme.{u}
  /-- The original puncture before the two retained localizations. -/
  seedA : Scheme.{u}
  /-- The original coefficient line before the two retained localizations. -/
  seedLine : Scheme.{u}
  /-- The original source map. -/
  seedP : seedY ⟶ seedLine
  /-- The original puncture map. -/
  seedAmap : seedA ⟶ seedLine
  /-- The composite of the two original source open inclusions. -/
  sourceToSeed : N.Y ⟶ seedY
  /-- The composite of the two original puncture open inclusions. -/
  punctureToSeed : N.A ⟶ seedA
  /-- The single shared composite coefficient-line restriction. -/
  lineToSeed : Spec (.of (Polynomial N.R)) ⟶ seedLine
  /-- The native source map commutes with the original restrictions. -/
  sourceSquare : N.p ≫ lineToSeed = sourceToSeed ≫ seedP
  /-- The native puncture map commutes with the same line restriction. -/
  punctureSquare : N.a ≫ lineToSeed = punctureToSeed ≫ seedAmap
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
namespace OriginalLocalizationHistory.SourceWitnesses
open AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification.NativeOriginalMiddleInput
attribute [local instance] OriginalLocalizationSeed.commRing OriginalLocalizationSeed.affineO
  OriginalLocalizationHistory.affineV

private theorem twoRestrictionSquares {C : Type*} [Category C]
    {Y₂ Y₁ Y₀ L₂ L₁ L₀ : C}
    (p₂ : Y₂ ⟶ L₂) (p₁ : Y₁ ⟶ L₁) (p₀ : Y₀ ⟶ L₀)
    (i₂ : Y₂ ⟶ Y₁) (i₁ : Y₁ ⟶ Y₀) (τV : L₂ ⟶ L₁) (τO : L₁ ⟶ L₀)
    (hV : p₂ ≫ τV = i₂ ≫ p₁) (hO : p₁ ≫ τO = i₁ ≫ p₀) :
    p₂ ≫ (τV ≫ τO) = (i₂ ≫ i₁) ≫ p₀ := by
  rw [← Category.assoc, hV, Category.assoc, hO, ← Category.assoc]

variable {H : OriginalLocalizationHistory.{u}} {B : H.BoundaryWitnesses}
  {k : Type u} [Field k] (W : H.SourceWitnesses B) (T : H.TargetWitnesses)
  (t : Spec Γ(H.V.toScheme, ⊤) ⟶ Spec (.of k)) [Smooth t]

/-- The native ancestry uses the same two actual opens and all original maps. -/
def toNativeAncestry : NativeAncestry (W.toNative T t) := by
  let : IsAffine H.V.toScheme := H.affineV
  let : IsAffine H.seed.O.toScheme := H.seed.affineO
  let τV := nativeAffineLineRestriction H.seed.R₁ H.V.ι
  let τO := nativeAffineLineRestriction H.seed.R H.seed.O.ι
  let i₂ := (boundaryBaseCoverOpen (boundaryLineProjection H.seed.R₁)
    H.seed.p₁ ⊤ H.V).ι
  let i₁ := (boundaryBaseCoverOpen (boundaryLineProjection H.seed.R)
    H.seed.p ⊤ H.seed.O).ι
  let j₂ := (boundaryBaseCoverOpen (boundaryLineProjection H.seed.R₁)
    H.seed.a₁ ⊤ H.V).ι
  let j₁ := (boundaryBaseCoverOpen (boundaryLineProjection H.seed.R)
    H.seed.a ⊤ H.seed.O).ι
  exact {
    seedY := H.seed.Y
    seedA := H.seed.A
    seedLine := Spec (.of (Polynomial H.seed.R))
    seedP := H.seed.p
    seedAmap := H.seed.a
    sourceToSeed := i₂ ≫ i₁
    punctureToSeed := j₂ ≫ j₁
    lineToSeed := τV ≫ τO
    sourceSquare := by
      exact twoRestrictionSquares H.p₂ H.seed.p₁ H.seed.p i₂ i₁ τV τO
        (@sourceNativeCoverMap_coordinate H.seed.R₁ _ H.V H.affineV _ H.seed.p₁)
        (sourceNativeCoverMap_coordinate H.seed.R H.seed.O H.seed.p)
    punctureSquare := by
      exact twoRestrictionSquares H.a₂ H.seed.a₁ H.seed.a j₂ j₁ τV τO
        (@sourceNativeCoverMap_coordinate H.seed.R₁ _ H.V H.affineV _ H.seed.a₁)
        (sourceNativeCoverMap_coordinate H.seed.R H.seed.O H.seed.a) }

end OriginalLocalizationHistory.SourceWitnesses
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
