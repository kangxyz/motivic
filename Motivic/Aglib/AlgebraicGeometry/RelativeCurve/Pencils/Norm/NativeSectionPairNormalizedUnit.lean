/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormParameterNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.NativeSectionPairParameterComponents
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionRegularity
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TwistedIdealRegularity
/-! # The original native section pairs normalize on their actual components

The source is literally the result of the two original coefficient restrictions.
Its actual finite component cover supplies integral parameter products; regularity
comes from the same source boundary-section data and target Serre divisors.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.NativeSectionPairNormalizedUnit`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeSectionPairTransferAction`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom RelativeProjectiveLine
open Scheme.RelativeAffineLineEtaleCompactification
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀] {Y₀ : Scheme.{u}} [IsAffine Y₀]
  (p₀ : Y₀ ⟶ Spec (.of (Polynomial R₀))) [Etale p₀] [QuasiCompact p₀] [IsSeparated p₀]
  (O₀ : (Spec (.of R₀)).Opens) [IsAffine O₀.toScheme]
  (V₀ : (Spec Γ(O₀.toScheme, ⊤)).Opens) [IsAffine V₀.toScheme]

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]

variable {A Z C D V WA : Scheme.{u}} [IsAffine A] [IsAffine V]
  [SmoothOfRelativeDimension 1 (boundaryLineProjection R)] [SmoothOfRelativeDimension 1 ((chart R
    0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]
  (f : C ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))) [IsFinite f] (j : (finalOriginalSource R₀ p₀
    O₀ V₀) ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ (f ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))]
  (p : (finalOriginalSource R₀ p₀ O₀ V₀) ⟶ (Spec (CommRingCat.of (Polynomial R)))) [Flat p] (hq
    : j ≫ (f ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) = p ≫ (boundaryLineProjection R))
  (hret : j ≫ f = p ≫ (chart R 0))
  (a : A ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsOpenImmersion a]
  (z : Z ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsClosedImmersion (z ≫ (chart R 0))]
  (s : Z ⟶ (finalOriginalSource R₀ p₀ O₀ V₀)) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (hsK : (s ≫ j) ≫ f = z ≫ (chart R 0))
  (e : SheafOfModules.unit (pullback (boundaryLineProjection R) (z ≫ (boundaryLineProjection
    R))).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget (boundaryLineProjection R) z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (c : BoundarySectionData (boundaryLineProjection R) (f ≫ (ProjectiveSpace.toSpec R (ULift.{u}
    (Fin 2)))) j p hq a z s hs H e ha d hd)
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ (ProjectiveSpace.toSpec
    R (ULift.{u} (Fin 2)))))]
  (hcover : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
  {DA : Scheme.{u}} (dA : DA ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))) [IsAffineHom dA]
  (hdA : Disjoint (Set.range (chart R 0)) (Set.range dA))
  (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
  (bE : (Scheme.residualMarkedFiberOpen f j (z ≫ (chart R 0)) s hsK).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j (z ≫ (chart R 0)) s hsK)
  (LA : LineBundle (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))
  (aA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))).val)
  (bA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶ LA.val)
  (iA : WA ⟶ pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) [IsOpenImmersion iA]
  (hFa : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart R 0) ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) iA
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))) aA)
  (hFb : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart R 0) ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) iA LA bA)
  (hpairA :
    let zA := coprod.desc (Hom.infinityProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
      (chart R 0) dA) (Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R (ULift.{u} (Fin
      2))) (chart R 0) z)
    pullbackSectionMap zA aA ≫ pullbackTensorMap zA LA.val
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine (ProjectiveSpace.toSpec R
        (ULift.{u} (Fin 2))) (chart R 0))).val =
    tensorUnitSection (pullbackSectionMap zA bA)
      (Hom.relativeFullBoundaryFrame (boundaryLineProjection R) (ProjectiveSpace.toSpec R
        (ULift.{u} (Fin 2))) (chart R 0) (𝟙 (Spec (CommRingCat.of (Polynomial R))))
        ((chart_toSpec R 0).trans (Category.id_comp (boundaryLineProjection R)).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)
  [IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R
      0) dA) (Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart
      R 0) z)) aA)]

variable [IsIso (pullbackSectionMap
  (Hom.fullBoundaryProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
    (chart R 0) dA z) bA)]

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] in
include hret hcover hbI hbE hFa hFb hpairA in
/-- The same original source and target section choices construct the normalized
R3 on each actual integral parameter component. All six regularity instances
and target integrality are derived here, not added as normalization premises. -/
theorem exists_nativeSectionPairNormalizedUnit
    (i : (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).I₀)
    (hfree : ∀ k : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R k), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (chart R k))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R k), ⊤)) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
    let T := pullback (α ≫ j ≫ f ≫ π) π
    let ρ := nativeSectionPairParameterComponentProductMap R₀ p₀ O₀ V₀ i R (j ≫ f ≫ π)
    let F := Hom.graphProductMap π f j
    let κ := ρ ≫ Hom.retainedParameterProductMap π f j (chart R 0) p hret
    let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π
      (chart R 0)))
    let MB := tensorLineBundle _ c.T (dualLineBundle _
      (Hom.relativeCompactificationGraphLine (f ≫ π) j))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π (chart R 0)) LA
      (Hom.idealInclusion (Hom.compactificationGraph π (chart R 0))) bA
    let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) j) c.T
      (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) j)) c.bS
    let afB := pullbackUnitMap (pullback.fst F ρ) (sectionDualFunctional _ MB c.aS)
    let cfB := pullbackUnitMap (pullback.fst F ρ) (sectionDualFunctional _ MB cB)
    let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
    let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
    let U := sectionPairNormParameterUnitDomain π f j (chart R 0) p hret
      LA aA bA c.T c.aS c.bS ρ
    let E := sectionPairParameterBoundary (ρ ≫ pullback.snd (j ≫ f ≫ π) π) dA
      (z ≫ chart R 0)
    ∃ (hT : IsIntegral T) (haB : Mono afB) (hcB : Mono cfB)
      (haA : Mono afA) (hcA : Mono cfA),
      letI := hT
      letI := haB
      letI := hcB
      letI := haA
      letI := hcA
      ∃ (hU : Nonempty U) (r : Γ(T, U)) (eU : _ ⟶ U.toScheme),
        eU ≫ U.ι = E ∧ IsUnit r ∧
        (letI := hU
         T.germToFunctionField U r =
          genericFiberLineRatioNorm (pullback.snd F ρ)
            (pullbackLineBundle (pullback.fst F ρ) (dualLineBundle _ MB)) afB cfB /
          genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA) ∧
        E.app U r = 1 := by
  dsimp only
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
  let T := pullback (α ≫ j ≫ f ≫ π) π
  let ρ := nativeSectionPairParameterComponentProductMap R₀ p₀ O₀ V₀ i R (j ≫ f ≫ π)
  let F := Hom.graphProductMap π f j
  let κ := ρ ≫ Hom.retainedParameterProductMap π f j (chart R 0) p hret
  let MA := tensorLineBundle _ LA (dualLineBundle _
    (Hom.relativeCompactificationGraphLine π (chart R 0)))
  let MB := tensorLineBundle _ c.T (dualLineBundle _
    (Hom.relativeCompactificationGraphLine (f ≫ π) j))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π (chart R 0)) LA
    (Hom.idealInclusion (Hom.compactificationGraph π (chart R 0))) bA
  let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) j) c.T
    (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) j)) c.bS
  obtain ⟨haB₀, hbB₀, _, _⟩ := BoundarySectionData.global_mono
    (boundaryLineProjection R) (f ≫ π) j p hq a z s hs H e ha d hd c v hcover
  let := haB₀
  let := hbB₀
  let := hFa.mono
  let := hFb.mono
  let : Mono (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) j)) :=
    Hom.idealInclusionMono _
  let : Mono (Hom.idealInclusion (Hom.compactificationGraph π (chart R 0))) :=
    Hom.idealInclusionMono _
  let := twistedIdealSection_mono _ (Hom.relativeCompactificationGraphLine (f ≫ π) j) c.T
    (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) j)) c.bS
  let := twistedIdealSection_mono _ (Hom.relativeCompactificationGraphLine π (chart R 0)) LA
    (Hom.idealInclusion (Hom.compactificationGraph π (chart R 0))) bA
  have haB : Mono (pullbackUnitMap (pullback.fst F ρ) (sectionDualFunctional _ MB c.aS)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  have hcB : Mono (pullbackUnitMap (pullback.fst F ρ) (sectionDualFunctional _ MB cB)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  have hbB : Mono (pullbackUnitMap (pullback.fst F ρ) (sectionDualFunctional _ c.T c.bS)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  have haA : Mono (pullbackUnitMap κ (sectionDualFunctional _ MA aA)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  have hcA : Mono (pullbackUnitMap κ (sectionDualFunctional _ MA cA)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  have hbA : Mono (pullbackUnitMap κ (sectionDualFunctional _ LA bA)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  let := haB
  let := hcB
  let := hbB
  let := haA
  let := hcA
  let := hbA
  let hT := (nativeSectionPairParameterComponent_product_normal R₀ p₀ O₀ V₀ i R
    (α ≫ j ≫ f ≫ π)).1
  let := hT
  let : IsIso (pullbackSectionMap
      (Hom.fullBoundaryProductMap (f ≫ π) j d s) c.aS) := c.a_unit
  let : IsIso (pullbackSectionMap
      (Hom.fullBoundaryProductMap (f ≫ π) j d s) c.bS) := c.b_unit
  let : IsIso (pullbackSectionMap
      (Hom.fullBoundaryProductMap π (chart R 0) dA z) aA) := by
    change IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π (chart R 0) dA)
        (Hom.graphBoundaryRestriction π (chart R 0) z)) aA)
    infer_instance
  have hcharts : ∀ x : ProjectiveSpace R (ULift.{u} (Fin 2)),
      ∃ k, x ∈ Set.range (chart R k) := by
    intro x
    have hx : x ∈ (⨆ k, (chart R k).opensRange) := by
      rw [iSup_chart_opensRange]
      trivial
    exact Opens.mem_iSup.mp hx
  refine ⟨hT, haB, hcB, haA, hcA, ?_⟩
  exact sectionPairNormParameter_exists_normalized_ratio π f j (chart R 0) p hret
    LA aA bA c.T c.aS c.bS (boundaryLineProjection R) (chart_toSpec R 0)
    z s hs H e d hd c.hA bE hbE dA hdA hpairA ρ bI hbI
    (fun _ : ULift.{u} (Fin 2) => CommRingCat.of (Polynomial R)) (chart R) hcharts hfree

end AlgebraicGeometry.Scheme.RelativeCurvePencil
