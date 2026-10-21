/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationInput
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairGlobalDifferenceZero
public import Motivic.Transfers.Presheaf.Sheafification.Image

/-! # Original-history middle relations

For an HI `P : PresheafWithTransfers.{u + 1} k` over a field, apply the
original difference-action supplier to the fixed target section bundle and
normalization history. Its normal Noetherian coefficient domain, whole free
charts, full boundary data and original graph maps remain in the displayed
inputs.

For the same `OriginalLocalizationHistory` source/target witnesses and smooth
coefficient structure map, `transfer_rawDifference_zero` supplies zero action
on `nisnevichImage P`. The resulting `middleRelations` combines that E3 datum
with E2/E4 and native E5 on the same original arrows.
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
universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
namespace NativeOriginalMiddleInput
attribute [local instance] commRing domain integrallyClosed noetherian affineY affineA affineV
  affineB finiteF openJ smoothJ flatP openA closedZChart openVB affineDA openIA
  smoothAlpha flatBeta smoothT
  Cor.nativeOriginalPairTransferActionSmooth
  nativeSectionPairDifferenceZeroSmoothRelativeDimension
  nativeOriginalMiddleInputSmooth nativeOriginalMiddleInputSmoothRelativeDimension1
  nativeOriginalMiddleInputSmoothRelativeDimension2

variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k)

/-- The raw action vanishes on an abstract native input
with its original two-localization source. -/
theorem transfer_rawDifference_zero_of_twoLocalizations
    (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    [IsNoetherianRing R₀] {Y₀ : Scheme.{u}} [IsAffine Y₀]
    (p₀ : Y₀ ⟶ Spec (.of (Polynomial R₀))) [Etale p₀] [QuasiCompact p₀] [IsSeparated p₀]
    (O₀ : (Spec (.of R₀)).Opens) [IsAffine O₀.toScheme]
    (V₀ : (Spec Γ(O₀.toScheme, ⊤)).Opens) [IsAffine V₀.toScheme]
    (hY : N.Y = finalOriginalSource R₀ p₀ O₀ V₀)
    (P : Motivic.PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    (nisnevichImage P).transfer N.toInput.rawDifference = 0 := by
  let := N.smoothA
  let := N.smoothVB
  rcases N with @⟨R, commRing, domain, integrallyClosed, noetherian, Y, A, Z, C, D, V, WA, DA,
    B, affineY, affineA, affineV, affineB, F, finiteF, j, openJ, smoothJ, p, flatP, hq, hret,
    a, openA, z, closedZChart, s, hs, H, hsK, e, ha, d, hd, source, vB, openVB, vA, hsmall,
    hcover, dA, affineDA, hdA, bI, hbI, bE, hbE, iA, openIA, target, αorig, smoothAlpha,
    βorig, flatBeta, horig, φorig, hφorig, hcoverA, t, smoothT, hpuncture, hfree⟩
  let := commRing
  let := domain
  let := integrallyClosed
  let := noetherian
  let := affineY
  let := affineA
  let := affineV
  let := affineB
  let := finiteF
  let := openJ
  let := smoothJ
  let := flatP
  let := openA
  let := closedZChart
  let := openVB
  let := affineDA
  let := openIA
  let := smoothAlpha
  let := flatBeta
  let := smoothT
  dsimp only at hY
  subst Y
  let : IsIso (pullbackSectionMap
      (coprod.desc (infinityProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
        (chart R 0) dA) (graphBoundaryRestriction
          (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0) z)) target.aA) :=
    target.unitA
  let := target.unitB
  exact nisnevichImage_transfer_nativeSectionPair_originalDifference_zero
    R₀ p₀ O₀ V₀ R F j p hq hret a z s hs H hsK e ha d hd source
    vB vA hsmall hcover dA hdA bI hbI bE hbE target.LA target.aA target.bA iA
    target.hFa target.hFb target.hpairA
    αorig βorig horig φorig hφorig hcoverA t P hP hfree

end NativeOriginalMiddleInput
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

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
attribute [local instance] Cor.nativeOriginalPairTransferActionSmooth
  nativeSectionPairDifferenceZeroSmoothRelativeDimension
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension1
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension2
variable {H : OriginalLocalizationHistory.{u}} {B : H.BoundaryWitnesses}
  {k : Type u} [Field k] (W : H.SourceWitnesses B) (T : H.TargetWitnesses)
  (t : Spec Γ(H.V.toScheme, ⊤) ⟶ Spec (.of k)) [Smooth t]
/-- Obtain the actual original raw-zero action internally, on the same native input. -/
theorem transfer_rawDifference_zero
    (P : Motivic.PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    (nisnevichImage P).transfer (W.toNative T t).toInput.rawDifference = 0 := by
  let N := W.toNative T t
  exact N.transfer_rawDifference_zero_of_twoLocalizations
    H.seed.R H.seed.p H.seed.O H.V rfl P hP

/-- The actual raw supplier supplies the missing E3 relation on this same input. -/
theorem middleRelations (P : Motivic.PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) :
    (W.toNative T t).toInput.MiddleRelations (W.toNative T t).aSite
      (W.toNative T t).delta (nisnevichImage P) := by
  exact ((W.toNative T t).middleRelations_of_rawDifference_zero (nisnevichImage P)
      (nisnevichImage_isA1Invariant P hP) (W.transfer_rawDifference_zero T t P hP))


end SourceWitnesses
end OriginalLocalizationHistory
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
