/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalTargetSectionWitnesses
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientNormalDomain
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFreeCharts
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedMarkedSquare
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedSourceInclusion
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.OriginalOverlapSectionChoice
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.OriginalRetainedSourceRestriction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NativeCorrectionBoundaryFactors
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativePunctureTransport
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve

/-! # Original two-localization history

The original seed, its two coefficient opens, boundary witnesses and section
choices retain their actual scheme maps and complete geometric hypotheses.
The source and target suppliers package the original choices. Current consumers
are the history-to-native construction and the original-representative history.

Intended upstream module: `OriginalLocalizationHistory` in
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine`.

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

open Scheme.RelativeAffineLineEtaleCompactification

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

/-- The original marked affine-line geometry and its first coefficient open. -/
structure OriginalLocalizationSeed where
  /-- The unchanged original R input. -/
  R : Type u
  /-- The unchanged original commRing input. -/
  [commRing : CommRing R]
  /-- The unchanged original domain input. -/
  [domain : IsDomain R]
  /-- The unchanged original normal input. -/
  [normal : IsIntegrallyClosed R]
  /-- The unchanged original noetherian input. -/
  [noetherian : IsNoetherianRing R]
  /-- The unchanged original Y input. -/
  Y : Scheme.{u}
  /-- The unchanged original A input. -/
  A : Scheme.{u}
  /-- The unchanged original Z input. -/
  Z : Scheme.{u}
  /-- The unchanged original affineY input. -/
  [affineY : IsAffine Y]
  /-- The unchanged original affineA input. -/
  [affineA : IsAffine A]
  /-- The unchanged original p input. -/
  p : Y ⟶ Spec (.of (Polynomial R))
  /-- The unchanged original etaleP input. -/
  [etaleP : Etale p]
  /-- The unchanged original quasiCompactP input. -/
  [quasiCompactP : QuasiCompact p]
  /-- The unchanged original separatedP input. -/
  [separatedP : IsSeparated p]
  /-- The unchanged original a input. -/
  a : A ⟶ Spec (.of (Polynomial R))
  /-- The unchanged original openA input. -/
  [openA : IsOpenImmersion a]
  /-- The unchanged original z input. -/
  z : Z ⟶ Spec (.of (Polynomial R))
  /-- The unchanged original closedZ input. -/
  [closedZ : IsClosedImmersion z]
  /-- The unchanged original finiteZ input. -/
  [finiteZ : IsFinite (z ≫ boundaryLineProjection R)]
  /-- The unchanged original s input. -/
  s : Z ⟶ Y
  /-- The unchanged original hs input. -/
  hs : s ≫ p = z
  /-- The unchanged original H input. -/
  H : IsPullback s (𝟙 _) p z
  /-- The unchanged original hz input. -/
  hz : Set.range z = (Set.range a)ᶜ
  /-- The unchanged original O input. -/
  O : (Spec (.of R)).Opens
  /-- The unchanged original affineO input. -/
  [affineO : IsAffine O.toScheme]

attribute [local instance] OriginalLocalizationSeed.commRing OriginalLocalizationSeed.domain
  OriginalLocalizationSeed.normal OriginalLocalizationSeed.noetherian
  OriginalLocalizationSeed.affineY OriginalLocalizationSeed.affineA
  OriginalLocalizationSeed.etaleP OriginalLocalizationSeed.quasiCompactP
  OriginalLocalizationSeed.separatedP OriginalLocalizationSeed.openA
  OriginalLocalizationSeed.closedZ OriginalLocalizationSeed.finiteZ
  OriginalLocalizationSeed.affineO

namespace OriginalLocalizationSeed
variable (S : OriginalLocalizationSeed.{u})

/-- The first coefficient ring. -/
abbrev R₁ := Γ(S.O.toScheme, ⊤)
/-- The first original normalized projective map. -/
def F₁ := boundaryBaseProjectiveMap S.R (ULift.{u} (Fin 2)) (toProjectiveLine S.R S.p) S.O
/-- The first original retained source inclusion. -/
def j₁ := boundaryBaseCoverInclusion (boundaryLineProjection S.R) S.p (projection S.R S.p)
  (inclusion S.R S.p) (inclusion_projection S.R S.p) ⊤ S.O
/-- The first native source map. -/
def p₁ := sourceNativeCoverMap S.R S.O S.p
/-- The first native puncture map. -/
def a₁ := sourceNativeCoverMap S.R S.O S.a
/-- The first native marked map. -/
def z₁ := targetNativeMarked S.R S.O S.z
/-- The first original marked lift. -/
def s₁ := boundaryBaseCoverLift (boundaryLineProjection S.R) S.p S.z S.s S.hs ⊤ S.O
  (fun _ _ => trivial)

/-- The unchanged first retained square. -/
theorem hret₁ : S.j₁ ≫ S.F₁ = S.p₁ ≫ chart S.R₁ 0 :=
  restricted_inclusion_toProjectiveLine S.R S.p S.O

end OriginalLocalizationSeed

/-- The same second coefficient open and the original common-choice square witnesses. -/
structure OriginalLocalizationHistory where
  /-- The original first-stage data. -/
  seed : OriginalLocalizationSeed.{u}
  /-- The original common second coefficient open. -/
  V : (Spec Γ(seed.O.toScheme, ⊤)).Opens
  /-- Affineness of that same open. -/
  [affineV : IsAffine V.toScheme]
  /-- The original common-choice base square, used in every dependent construction. -/
  hq₁ : seed.j₁ ≫ (seed.F₁ ≫ ProjectiveSpace.toSpec seed.R₁ (ULift.{u} (Fin 2))) =
    seed.p₁ ≫ boundaryLineProjection seed.R₁
  /-- The original common-choice marked equation. -/
  hs₁ : seed.s₁ ≫ seed.p₁ = seed.z₁

attribute [local instance] OriginalLocalizationHistory.affineV

namespace OriginalLocalizationHistory
variable (H : OriginalLocalizationHistory.{u})

/-- The unchanged final coefficient ring. -/
abbrev R₂ := Γ(H.V.toScheme, ⊤)
/-- The original whole final line projection. -/
def q₂ := boundaryLineProjection H.R₂
/-- The original projective projection. -/
def π₂ := ProjectiveSpace.toSpec H.R₂ (ULift.{u} (Fin 2))
/-- The original full affine chart. -/
def jA₂ := chart H.R₂ 0
/-- The unique final source, fixed by its original history. -/
abbrev Y₂ := finalOriginalSource H.seed.R H.seed.p H.seed.O H.V
/-- The second original projective map. -/
def F₂ := boundaryBaseProjectiveMap H.seed.R₁ (ULift.{u} (Fin 2)) H.seed.F₁ H.V
/-- The second original retained inclusion. -/
def j₂ := boundaryBaseCoverInclusion (boundaryLineProjection H.seed.R₁) H.seed.p₁
  (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
  H.seed.j₁ H.hq₁ ⊤ H.V
/-- The second native source map. -/
def p₂ := sourceNativeCoverMap H.seed.R₁ H.V H.seed.p₁
/-- The second native puncture map. -/
def a₂ := sourceNativeCoverMap H.seed.R₁ H.V H.seed.a₁
/-- The second native marking. -/
def z₂ := targetNativeMarked H.seed.R₁ H.V H.seed.z₁
/-- The second original marked lift. -/
def s₂ := boundaryBaseCoverLift (boundaryLineProjection H.seed.R₁) H.seed.p₁
  H.seed.z₁ H.seed.s₁ H.hs₁ ⊤ H.V (fun _ _ => trivial)
/-- The original retained source restriction. -/
def vB := originalRetainedSourceRestriction (boundaryLineProjection H.seed.R₁)
  H.seed.p₁ H.seed.a₁ (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
  H.seed.j₁ H.hq₁ H.V
/-- The original retained puncture restriction. -/
def vA := originalRetainedPunctureRestriction (boundaryLineProjection H.seed.R₁)
  H.seed.p₁ H.seed.a₁ (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
  H.seed.j₁ H.hq₁ H.V
/-- The original overlap's source projection. -/
def αorig := pullback.fst
  (boundaryBaseCoverMap (boundaryLineProjection H.seed.R₁) H.seed.p₁ ⊤ H.V)
  (boundaryBaseCoverMap (boundaryLineProjection H.seed.R₁) H.seed.a₁ ⊤ H.V)
/-- The original overlap's puncture projection. -/
def βorig := pullback.snd
  (boundaryBaseCoverMap (boundaryLineProjection H.seed.R₁) H.seed.p₁ ⊤ H.V)
  (boundaryBaseCoverMap (boundaryLineProjection H.seed.R₁) H.seed.a₁ ⊤ H.V)

/-- The entire second retained square on a shared arbitrary history. -/
theorem hret₂ : H.j₂ ≫ H.F₂ = H.p₂ ≫ H.jA₂ := by
  dsimp only [j₂, p₂, jA₂]
  let τ := ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap H.seed.R₁ H.V.ι)
    (ULift.{u} (Fin 2))
  let : IsOpenImmersion τ := MorphismProperty.of_isPullback
    (ConstantCurve.affineSourceProjectiveSquare H.seed.R₁ (ULift.{u} (Fin 2)) H.V.ι).flip
    inferInstance
  apply (cancel_mono τ).mp
  simp only [Category.assoc]
  change _ ≫ (ConstantCurve.affineSourceToProjectiveSpace H.seed.R₁ _ H.V.ι H.seed.F₁ ≫ _) = _
  rw [ConstantCurve.affineSourceToProjectiveSpace_map]
  rw [← Category.assoc, boundaryBaseCoverInclusion_snd, Category.assoc,
    H.seed.hret₁, chart_map, ← Category.assoc, sourceNativeCoverMap_coordinate_assoc]
  simp only [Category.assoc]

/-- The marked lift remains over the original native line. -/
theorem hs₂ : H.s₂ ≫ H.p₂ = H.z₂ :=
  sourceNativeCoverLift_map H.seed.R₁ H.V H.seed.z₁ H.seed.p₁ H.seed.s₁ H.hs₁

/-- The full original marked square remains Cartesian. -/
theorem markedSquare : IsPullback H.s₂ (𝟙 _) H.p₂ H.z₂ :=
  sourceNativeCoverLift_isPullback H.seed.R₁ H.V H.seed.z₁ H.seed.p₁ H.seed.s₁ H.hs₁
    (sourceNativeCoverLift_isPullback H.seed.R H.seed.O H.seed.z H.seed.p
      H.seed.s H.seed.hs H.seed.H)

/-- The first original marked triangle. -/
theorem hsK₁ : (H.seed.s₁ ≫ H.seed.j₁) ≫ H.seed.F₁ = H.seed.z₁ ≫ chart H.seed.R₁ 0 := by
  rw [Category.assoc, H.seed.hret₁, ← Category.assoc, H.hs₁]

/-- The second original marked triangle. -/
theorem hsK₂ : (H.s₂ ≫ H.j₂) ≫ H.F₂ = H.z₂ ≫ H.jA₂ := by
  rw [Category.assoc, H.hret₂, ← Category.assoc, H.hs₂]

/-- The original retained restrictions form their native square. -/
theorem hsmall : H.vB ≫ H.p₂ = H.vA ≫ H.a₂ := by
  simpa only [vB, vA, p₂, a₂, sourceNativeCoverMap, ← Category.assoc] using
    congrArg (fun f => f ≫ (sourceNativeParameterIso H.seed.R₁ H.V).hom)
      (originalRetainedRestriction_square (boundaryLineProjection H.seed.R₁)
        H.seed.p₁ H.seed.a₁
        (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
        H.seed.j₁ H.hq₁ H.V)

/-- The original overlap square after the same coordinate isomorphism. -/
theorem horig : H.αorig ≫ H.p₂ = H.βorig ≫ H.a₂ := by
  simpa only [αorig, βorig, p₂, a₂, sourceNativeCoverMap, ← Category.assoc] using
    congrArg (fun f => f ≫ (sourceNativeParameterIso H.seed.R₁ H.V).hom)
      (pullback.condition
        (f := boundaryBaseCoverMap (boundaryLineProjection H.seed.R₁) H.seed.p₁ ⊤ H.V)
        (g := boundaryBaseCoverMap (boundaryLineProjection H.seed.R₁) H.seed.a₁ ⊤ H.V))

/-- The actual first compactification, not a newly normalized source. -/
abbrev C₁ := boundaryBaseCompactification (projection H.seed.R H.seed.p) H.seed.O
/-- The whole original infinity before the second restriction. -/
def dA₁ := neighborhoodBoundaryInclusion H.seed.R₁ ⊤
/-- The same full original infinity after the second restriction. -/
def dA₂ := targetNativeInfinity H.seed.R₁ H.V H.dA₁

/-- The first infinity is disjoint from the original affine chart. -/
theorem hdA₁ : Disjoint (Set.range (chart H.seed.R₁ 0)) (Set.range H.dA₁) := by
  rw [dA₁, range_neighborhoodBoundaryInclusion]
  apply Set.disjoint_left.mpr
  rintro _ ⟨y, rfl⟩ hmem
  exact hmem ⟨y, trivial, rfl⟩

/-- The same disjointness after the original second localization. -/
theorem hdA₂ : Disjoint (Set.range H.jA₂) (Set.range H.dA₂) :=
  targetNativeInfinity_disjoint H.seed.R₁ H.V H.dA₁ H.hdA₁

/-- The unchanged marked complement after the first localization. -/
theorem hz₁ : Set.range H.seed.z₁ = (Set.range H.seed.a₁)ᶜ :=
  sourceNativeCoverMap_marked_complement H.seed.R H.seed.O H.seed.a H.seed.z H.seed.hz

/-- The actual puncture complement, including the empty-puncture case. -/
theorem hpuncture : (Set.range H.a₂)ᶜ ⊆ Set.range H.z₂ := by
  rw [show Set.range H.z₂ = (Set.range H.a₂)ᶜ from
    sourceNativeCoverMap_marked_complement H.seed.R₁ H.V H.seed.a₁ H.seed.z₁ H.hz₁]

/-- The original native puncture, full infinity and marking cover the projective line. -/
theorem hcoverA (x : ProjectiveSpace H.R₂ (ULift.{u} (Fin 2))) :
    x ∈ Set.range (H.a₂ ≫ H.jA₂) ∨ x ∈ Set.range H.dA₂ ∨
      x ∈ Set.range (H.z₂ ≫ H.jA₂) := by
  rcases targetNative_cover H.seed.R₁ H.V H.seed.z₁ H.dA₁
      (H.seed.a₁ ≫ chart H.seed.R₁ 0)
      (originalPuncture_boundary_cover H.seed.R₁ H.seed.a₁ H.seed.z₁ H.hz₁) x with hv | hd | hz
  · obtain ⟨w, hw⟩ := hv
    left
    refine ⟨(nativePunctureTransport H.seed.R₁ H.V H.seed.a₁).hom w, ?_⟩
    have he := congrArg (fun f => f w)
      (nativePunctureTransport_chart H.seed.R₁ H.V H.seed.a₁)
    exact he.trans hw
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr hz)

local instance (S : OriginalLocalizationSeed.{u}) : IsFinite S.F₁ :=
  boundaryBaseProjectiveMap_finite S.R (ULift.{u} (Fin 2)) (toProjectiveLine S.R S.p) S.O

local instance : IsFinite H.F₂ :=
  boundaryBaseProjectiveMap_finite H.seed.R₁ (ULift.{u} (Fin 2)) H.seed.F₁ H.V

/-- The original boundary and free-chart witnesses, indexed by their unique geometry. -/
structure BoundaryWitnesses where
  /-- The first localization retains the original generic point. -/
  hηO : genericPoint (Spec (.of H.seed.R)) ∈ H.seed.O
  /-- The original second-localization point. -/
  x : Spec Γ(H.seed.O.toScheme, ⊤)
  /-- That same point belongs to the original second open. -/
  hxV : x ∈ H.V
  /-- The original chart-freeness localization element. -/
  r : H.seed.R
  /-- The original first open lies in that basic open. -/
  hOr : H.seed.O ≤ PrimeSpectrum.basicOpen r
  /-- Both original free charts with their literal scalar algebra structures. -/
  hfree₀ : ∀ i : ULift.{u} (Fin 2),
    let w := chart (Localization.Away r) i ≫
      ProjectiveSpace.map (algebraMap H.seed.R (Localization.Away r)) (ULift.{u} (Fin 2))
    let : Algebra (Polynomial (Localization.Away r))
        Γ(pullback (toProjectiveLine H.seed.R H.seed.p) w, ⊤) :=
      (AlgebraicGeometry.FiniteSchemeNormBaseChange.scalarMap (pullback.snd _ w)).toAlgebra
    Module.Free (Polynomial (Localization.Away r))
      Γ(pullback (toProjectiveLine H.seed.R H.seed.p) w, ⊤)
  /-- The original first boundary scheme. -/
  D : Scheme.{u}
  /-- Its unchanged map into the first compactification. -/
  d : D ⟶ H.C₁
  /-- The original closed boundary witness. -/
  [closedD : IsClosedImmersion d]
  /-- The FULL complement equality, not merely disjointness. -/
  hdr : Set.range d = (Set.range H.seed.j₁)ᶜ
  /-- The original finite-over-base boundary witness. -/
  [finiteD : IsFinite (d ≫ (H.seed.F₁ ≫
    ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2))))]
  /-- The original complete infinity factor. -/
  bI : pullback H.seed.F₁ H.dA₁ ⟶ D
  /-- Its original scheme-theoretic factorization. -/
  hbI : bI ≫ d = pullback.fst H.seed.F₁ H.dA₁
  /-- The original complete residual marked-fiber factor. -/
  bE : (Scheme.residualMarkedFiberOpen H.seed.F₁ H.seed.j₁
    (H.seed.z₁ ≫ chart H.seed.R₁ 0) H.seed.s₁ H.hsK₁).toScheme ⟶ D
  /-- Its original scheme-theoretic factorization. -/
  hbE : bE ≫ d = Scheme.residualMarkedFiberMap H.seed.F₁ H.seed.j₁
    (H.seed.z₁ ≫ chart H.seed.R₁ 0) H.seed.s₁ H.hsK₁

namespace BoundaryWitnesses
attribute [local instance] closedD finiteD
variable {H : OriginalLocalizationHistory.{u}} (B : H.BoundaryWitnesses)

include B in
/-- The original first coefficient ring properties, derived internally. -/
theorem ringProperties₁ : IsDomain H.seed.R₁ ∧ IsIntegrallyClosed H.seed.R₁ ∧
    IsNoetherianRing H.seed.R₁ :=
  originalCoefficientRing_properties H.seed.R H.seed.O
    (genericPoint (Spec (.of H.seed.R))) B.hηO

include B in
/-- The original final coefficient ring properties, derived internally. -/
theorem ringProperties₂ : IsDomain H.R₂ ∧ IsIntegrallyClosed H.R₂ ∧ IsNoetherianRing H.R₂ :=
  finalCoefficientRing_properties H.seed.R H.seed.O
    (genericPoint (Spec (.of H.seed.R))) B.hηO H.V B.x B.hxV

/-- The same full original boundary after the second localization. -/
def d₂ := boundaryBaseWholeMap
  (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2))) B.d H.V
/-- The unchanged infinity factor after the same localization. -/
def bI₂ := nativeCorrectionInfinityFactor H.seed.R₁ H.seed.F₁ B.d H.dA₁ B.bI B.hbI H.V
/-- The actual infinity factor equation. -/
theorem hbI₂ : B.bI₂ ≫ B.d₂ = pullback.fst H.F₂ H.dA₂ :=
  nativeCorrectionInfinityFactor_inclusion H.seed.R₁ H.seed.F₁ B.d H.dA₁ B.bI B.hbI H.V
/-- The unchanged residual factor, including its full scheme structure. -/
def bE₂ := nativeCorrectionResidualFactor H.seed.R₁ H.seed.F₁ B.d H.V H.seed.p₁
  H.seed.j₁ H.hq₁ H.seed.z₁ H.seed.s₁ H.hs₁ H.hsK₁ B.bE B.hbE
/-- The actual residual factor equation on the same second marked triangle. -/
theorem hbE₂ : B.bE₂ ≫ B.d₂ =
    Scheme.residualMarkedFiberMap H.F₂ H.j₂ (H.z₂ ≫ H.jA₂) H.s₂ H.hsK₂ :=
  nativeCorrectionResidualFactor_inclusion H.seed.R₁ H.seed.F₁ B.d H.V H.seed.p₁
    H.seed.j₁ H.hq₁ H.seed.z₁ H.seed.s₁ H.hs₁ H.hsK₁ B.bE B.hbE

include B in
/-- Both final free charts are inherited from the original free-chart localization. -/
theorem hfree₂ : ∀ i : ULift.{u} (Fin 2),
    let : Algebra (Polynomial H.R₂) Γ(pullback H.F₂ (chart H.R₂ i), ⊤) :=
      (AlgebraicGeometry.FiniteSchemeNormBaseChange.scalarMap (pullback.snd _ _)).toAlgebra
    Module.Free (Polynomial H.R₂) Γ(pullback H.F₂ (chart H.R₂ i), ⊤) :=
  finalCoefficient_chart_sections_free H.seed.R B.r H.seed.O B.hOr H.V
    (toProjectiveLine H.seed.R H.seed.p) B.hfree₀

/-- Original first overlap coverage from the actual complement equality. -/
theorem hc₁ (y : H.C₁) :
    y ∈ Set.range (pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) ∨
      y ∈ Set.range B.d ∨ y ∈ Set.range (H.seed.s₁ ≫ H.seed.j₁) := by
  exact originalOverlap_boundary_cover H.seed.R₁ H.seed.p₁ H.seed.a₁ H.seed.z₁ H.seed.s₁
    (sourceNativeCoverLift_isPullback H.seed.R H.seed.O H.seed.z H.seed.p
      H.seed.s H.seed.hs H.seed.H) H.hz₁ H.seed.j₁ B.d B.hdr y

/-- The same retained source inclusion into the second compactification. -/
theorem hvRet : H.vB ≫ H.j₂ = boundaryBaseRetainedTarget
    (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
    H.V (pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) :=
  originalRetainedSourceRestriction_inclusion (boundaryLineProjection H.seed.R₁)
    H.seed.p₁ H.seed.a₁
    (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
    H.seed.j₁ H.hq₁ H.V

/-- Full second source coverage, not an added history hypothesis. -/
theorem hc₂ (y : boundaryBaseCompactification
    (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2))) H.V) :
    y ∈ Set.range (H.vB ≫ H.j₂) ∨ y ∈ Set.range B.d₂ ∨
      y ∈ Set.range (H.s₂ ≫ H.j₂) := by
  rw [hvRet (H := H)]
  exact boundaryBaseSourceBoundary_cover (boundaryLineProjection H.seed.R₁)
    H.seed.p₁ H.seed.z₁ H.seed.s₁ H.hs₁
    (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
    H.seed.j₁ H.hq₁ B.d ⊤ H.V (fun _ _ => trivial)
    (pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) B.hc₁ y

end BoundaryWitnesses

local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- The owning affine chart is the original open immersion. -/
local instance chartOpen : IsOpenImmersion H.jA₂ := chart_isOpenImmersion H.R₂ 0

/-- The same chart projection has relative dimension one. -/
local instance chartSmooth : SmoothOfRelativeDimension 1 (H.jA₂ ≫ H.π₂) := by
  dsimp only [jA₂, π₂]
  rw [chart_toSpec]
  infer_instance

/-- The original first source remains etale. -/
local instance seedEtale (S : OriginalLocalizationSeed.{u}) : Etale S.p₁ :=
  sourceNativeCoverMap_etale S.R S.O S.p
/-- The original first puncture stays open. -/
local instance seedOpen (S : OriginalLocalizationSeed.{u}) : IsOpenImmersion S.a₁ :=
  sourceNativeCoverMap_open S.R S.O S.a
/-- The original first source inclusion stays open. -/
local instance seedInclusionOpen (S : OriginalLocalizationSeed.{u}) : IsOpenImmersion S.j₁ :=
  boundaryBaseCoverInclusion_open (boundaryLineProjection S.R) S.p (projection S.R S.p)
    (inclusion S.R S.p) (inclusion_projection S.R S.p) ⊤ S.O
/-- The original marking remains finite over the first base. -/
local instance seedMarkedFinite (S : OriginalLocalizationSeed.{u}) :
    IsFinite (S.z₁ ≫ boundaryLineProjection S.R₁) :=
  targetNativeMarked_finite S.R S.O S.z
/-- The original marking stays closed. -/
local instance seedMarkedClosed (S : OriginalLocalizationSeed.{u}) : IsClosedImmersion S.z₁ :=
  targetNativeMarked_closed S.R S.O S.z
/-- The final original source remains etale. -/
local instance sourceEtale : Etale H.p₂ :=
  sourceNativeCoverMap_etale H.seed.R₁ H.V H.seed.p₁
/-- The final original puncture stays open. -/
local instance punctureOpen : IsOpenImmersion H.a₂ :=
  sourceNativeCoverMap_open H.seed.R₁ H.V H.seed.a₁
/-- The original final inclusion stays open. -/
local instance inclusionOpen : IsOpenImmersion H.j₂ :=
  boundaryBaseCoverInclusion_open (boundaryLineProjection H.seed.R₁) H.seed.p₁
    (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
    H.seed.j₁ H.hq₁ ⊤ H.V
/-- The final original source has the original relative dimension. -/
local instance sourceSmooth : SmoothOfRelativeDimension 1 (H.j₂ ≫ (H.F₂ ≫ H.π₂)) :=
  boundaryBaseCoverInclusion_projective_smooth H.seed.R₁ (ULift.{u} (Fin 2))
    (boundaryLineProjection H.seed.R₁) H.seed.p₁ H.seed.F₁ H.seed.j₁ H.hq₁ ⊤ H.V
/-- The original line projection has relative dimension one. -/
local instance lineSmooth : SmoothOfRelativeDimension 1 H.q₂ := by
  dsimp only [q₂]
  infer_instance
/-- The original line projection is separated. -/
local instance lineSeparated : IsSeparated H.q₂ := by
  dsimp only [q₂]
  infer_instance
/-- The actual compactification remains proper over the final base. -/
local instance compactificationProper : IsProper (H.F₂ ≫ H.π₂) := by
  dsimp only [π₂]
  infer_instance
/-- The unique canonical frame on the final native marking. -/
def e₂ := targetNativeCanonicalFrame H.seed.R₁ H.V H.seed.z₁
/-- The original retained product, not the small puncture inclusion. -/
def iA := retainedProductInclusion (H.jA₂ ≫ H.π₂) H.π₂
  (targetNativeRetained H.seed.R₁ H.V (H.seed.a₁ ≫ chart H.seed.R₁ 0))
/-- The original retained product inclusion is open. -/
local instance retainedProductOpen : IsOpenImmersion H.iA :=
  targetNativeRetainedProduct_chart_open H.seed.R₁ H.V H.seed.a₁

/-- The one original source-section choice on the shared full history. -/
structure SourceWitnesses (B : H.BoundaryWitnesses) where
  /-- The original source section square witness. -/
  hqn : H.j₂ ≫ (H.F₂ ≫ H.π₂) = H.p₂ ≫ H.q₂
  /-- The original source section disjointness witness. -/
  han : Disjoint (Set.range H.a₂) (Set.range H.z₂)
  /-- The original whole-boundary disjointness witness. -/
  hdn : Disjoint (Set.range H.j₂) (Set.range B.d₂)
  /-- The original source section datum, chosen exactly once. -/
  source : BoundarySectionData H.q₂ (H.F₂ ≫ H.π₂) H.j₂ H.p₂ hqn H.a₂ H.z₂ H.s₂
    H.hs₂ H.markedSquare H.e₂ han B.d₂ hdn


/-- The original target tuple is one application of the free geometric schema. -/
abbrev TargetWitnesses := @OriginalTargetSectionWitnesses.{u}
  (Γ(H.V.toScheme, ⊤)).carrier (Γ(H.V.toScheme, ⊤)).commRing _ _ _
  H.z₂ H.e₂ H.dA₂ H.hdA₂ H.iA


/-- The original marking is closed also in the original projective line. -/
local instance seedProjectiveMarked (S : OriginalLocalizationSeed.{u}) :
    IsClosedImmersion (S.z ≫ chart S.R 0) := by
  let : IsProper ((S.z ≫ chart S.R 0) ≫
      ProjectiveSpace.toSpec S.R (ULift.{u} (Fin 2))) := by
    rw [Category.assoc, chart_toSpec]
    infer_instance
  let : IsProper (S.z ≫ chart S.R 0) :=
    IsProper.of_comp _ (ProjectiveSpace.toSpec S.R (ULift.{u} (Fin 2)))
  exact IsClosedImmersion.of_isPreimmersion _
    (S.z ≫ chart S.R 0).isClosedMap.isClosed_range

/-- The first marked projective immersion is unchanged. -/
local instance firstProjectiveMarked (S : OriginalLocalizationSeed.{u}) :
    IsClosedImmersion (S.z₁ ≫ chart S.R₁ 0) :=
  targetNativeMarked_chart_closed S.R S.O S.z

/-- The final marked projective immersion is unchanged. -/
local instance finalProjectiveMarked : IsClosedImmersion (H.z₂ ≫ H.jA₂) :=
  targetNativeMarked_chart_closed H.seed.R₁ H.V H.seed.z₁

/-- The original first source is affine. -/
local instance firstSourceAffine (S : OriginalLocalizationSeed.{u}) :
    IsAffine (boundaryBaseCoverOpen (boundaryLineProjection S.R) S.p ⊤ S.O).toScheme :=
  boundaryBaseCoverOpen_affine_instance (boundaryLineProjection S.R) S.p ⊤ S.O

/-- The original first puncture is affine. -/
local instance firstPunctureAffine (S : OriginalLocalizationSeed.{u}) :
    IsAffine (boundaryBaseCoverOpen (boundaryLineProjection S.R) S.a ⊤ S.O).toScheme :=
  boundaryBaseCoverOpen_affine_instance (boundaryLineProjection S.R) S.a ⊤ S.O

/-- The final original source is affine. -/
local instance finalSourceAffine : IsAffine H.Y₂ :=
  boundaryBaseCoverOpen_affine_instance (boundaryLineProjection H.seed.R₁) H.seed.p₁ ⊤ H.V

/-- The final original puncture is affine. -/
local instance finalPunctureAffine :
    IsAffine (boundaryBaseCoverOpen (boundaryLineProjection H.seed.R₁) H.seed.a₁ ⊤ H.V).toScheme :=
  boundaryBaseCoverOpen_affine_instance (boundaryLineProjection H.seed.R₁) H.seed.a₁ ⊤ H.V

/-- The original retained overlap is affine. -/
local instance retainedAffine : IsAffine
    ((((pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) ≫
      (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))) ⁻¹ᵁ H.V).toScheme) :=
  boundaryBaseRetainedOpen_affine H.V
    (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2)))
    (pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁)

/-- The original overlap of the two final opens is affine. -/
local instance overlapAffine :
    IsAffine (boundaryBaseOverlap (boundaryLineProjection H.seed.R₁)
      H.seed.p₁ H.seed.a₁ ⊤ H.V) :=
  boundaryBaseOverlap_affine_instance (boundaryLineProjection H.seed.R₁)
    H.seed.p₁ H.seed.a₁ ⊤ H.V

/-- The retained source restriction is open, by its unchanged inclusion identity. -/
local instance retainedOpen : IsOpenImmersion H.vB := by
  let : IsOpenImmersion (H.vB ≫ H.j₂) := by
    rw [BoundaryWitnesses.hvRet (H := H)]
    infer_instance
  exact IsOpenImmersion.of_comp H.vB H.j₂

/-- The unchanged overlap projection is smooth. -/
local instance overlapSmooth : Smooth H.αorig := by
  dsimp only [αorig]
  infer_instance

/-- The unchanged other overlap projection is flat. -/
local instance overlapFlat : Flat H.βorig := by
  dsimp only [βorig]
  infer_instance

/-- The unchanged infinity map is affine. -/
local instance infinityAffine : IsAffineHom H.dA₂ := by
  dsimp only [dA₂, dA₁]
  infer_instance

/-- The unique unchanged original overlap map. -/
def φorig := boundaryBaseOverlapTarget (boundaryLineProjection H.seed.R₁)
  H.seed.p₁ H.seed.a₁ ⊤ H.V
  (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2))) H.seed.j₁ H.hq₁
  (pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) (𝟙 _) (Category.id_comp _)

/-- Its original inclusion equation. -/
theorem hφorig : H.φorig ≫ (H.vB ≫ H.j₂) = H.αorig ≫ H.j₂ := by
  rw [BoundaryWitnesses.hvRet (H := H)]
  exact boundaryBaseOverlapTarget_inclusion (boundaryLineProjection H.seed.R₁)
    H.seed.p₁ H.seed.a₁ ⊤ H.V
    (H.seed.F₁ ≫ ProjectiveSpace.toSpec H.seed.R₁ (ULift.{u} (Fin 2))) H.seed.j₁ H.hq₁
    (pullback.fst H.seed.p₁ H.seed.a₁ ≫ H.seed.j₁) (𝟙 _) (Category.id_comp _)


/-- The rich target supplier on the fixed first and second coefficient choices. -/
abbrev TargetSections :=
  NativeTargetBoundarySections (R := H.seed.R₁) (z := H.seed.z₁)
      (V := H.V) (d₀ := H.dA₁) (hd₀ := H.hdA₁)
      (v₀ := H.seed.a₁ ≫ chart H.seed.R₁ 0)

/-- Apply the existing original supplier once on this same history. -/
theorem nonemptyTargetWitnesses (h : H.TargetSections) :
    Nonempty H.TargetWitnesses := by
  exact (nonempty_originalTargetSectionWitnesses H.seed.R₁ H.V H.seed.z₁
      H.dA₁ H.hdA₁ (H.seed.a₁ ≫ chart H.seed.R₁ 0) h)

/-- The rich source supplier uses the boundary and maps of this same history. -/
abbrev SourceSections (B : H.BoundaryWitnesses) :=
  NativeSourceBoundarySections
      (R := H.seed.R₁) (ι := ULift.{u} (Fin 2))
      (p := H.seed.p₁) (a := H.seed.a₁) (f := H.seed.F₁) (j := H.seed.j₁)
      (hj := H.hq₁) (z := H.seed.z₁) (s := H.seed.s₁) (hs := H.hs₁)
      (H := sourceNativeCoverLift_isPullback H.seed.R H.seed.O H.seed.z H.seed.p
        H.seed.s H.seed.hs H.seed.H) (d := B.d) (V := H.V)

/-- Package the original rich source supplier without another section choice. -/
theorem nonempty_sourceWitnesses (H : OriginalLocalizationHistory.{u}) (B : H.BoundaryWitnesses)
    (h : H.SourceSections B) :
    Nonempty (H.SourceWitnesses B) := by
  obtain ⟨hqn, han, hdn, hframe, ⟨c⟩, hdual⟩ := h
  exact ⟨{ hqn := hqn, han := han, hdn := hdn, source := c }⟩


end OriginalLocalizationHistory
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
