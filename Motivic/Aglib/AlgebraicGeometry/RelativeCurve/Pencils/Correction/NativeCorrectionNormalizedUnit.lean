/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NormalizedUnit
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionRegularity
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TwistedIdealRegularity
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.AffineParameterNormal
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.OpenChartSection
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
/-! # Normalize the same native correction sections on the original puncture

The original source record and target Serre divisor records produce regularity.
The nonempty original puncture is integral because it is open in an affine line
over the chosen normal domain, not because normal schemes are always integral.
The original two free projective charts are used unchanged.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NativeCorrectionNormalizedUnit`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeCorrectionNormAction`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The nonempty original puncture gives an integral normal projective target.
No integrality is imposed on the finite covering source. -/
theorem nativeCorrectionParameter_normal
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    {A : Scheme.{u}} [IsAffine A] [Nonempty A]
    (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a] :
    IsIntegral (pullback (a ≫ boundaryLineProjection R)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ∧
    IsNoetherian (pullback (a ≫ boundaryLineProjection R)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ∧
    ∀ x : (pullback (a ≫ boundaryLineProjection R)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) : Scheme.{u}),
      IsIntegrallyClosed ((pullback (a ≫ boundaryLineProjection R)
        (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).presheaf.stalk x) := by
  let : IsIntegral A := isIntegral_of_isOpenImmersion a
  let (x : A) : IsIntegrallyClosed (A.presheaf.stalk x) := by
    let := (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec (Polynomial R) (a x)).1
    exact IsIntegrallyClosed.of_equiv (asIso (a.stalkMap x)).commRingCatIsoToRingEquiv
  let : Nonempty (⊤ : A.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  let : IsIntegrallyClosed Γ(A, ⊤) :=
    A.isIntegrallyClosed_sections_of_isAffineOpen ⊤ (isAffineOpen_top A)
  let : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian a
  let : IsNoetherianRing Γ(A, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top A⟩
  exact affineParameterPullback_normal R (a ≫ boundaryLineProjection R)

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]

variable {Y A Z C D V WA : Scheme.{u}} [IsAffine Y] [IsAffine A] [Nonempty A] [IsAffine V]
  [SmoothOfRelativeDimension 1 (boundaryLineProjection R)] [SmoothOfRelativeDimension 1 ((chart R
    0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]
  (f : C ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ (f ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))]
  (p : Y ⟶ (Spec (CommRingCat.of (Polynomial R)))) [Flat p] (hq : j ≫ (f ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) = p ≫ (boundaryLineProjection R))
  (hret : j ≫ f = p ≫ (chart R 0))
  (a : A ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsOpenImmersion a]
  (z : Z ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsClosedImmersion (z ≫ (chart R 0))]
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
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

include hret hcover hbI hbE hFa hFb hpairA in
/-- The original native section records produce the complete normalized R5.
Regularity, target integrality and a good-open point are outputs, not premises. -/
theorem exists_nativeCorrectionNormalizedUnit
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (chart R i))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R i), ⊤)) :
    let T := pullback (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
      2)))
    let F := Hom.normProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) f (a ≫
      (boundaryLineProjection R))
    let τ := Hom.retainedNormParameterMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
      (boundaryLineProjection R)) (chart R 0) a
      (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
    let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)) LA
      (Hom.idealInclusion (Hom.compactificationGraph (ProjectiveSpace.toSpec R (ULift.{u} (Fin
        2))) (chart R 0))) bA
    let L := pullbackLineBundle τ (dualLineBundle _ M)
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
    let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
    let W := functionalNormProductUnitDomain F (dualLineBundle _ c.N)
      (dualLineBundle _ c.N) nφ dφ L L aφ cφ
    let E := pullback (a ≫ (boundaryLineProjection R)) (dA ≫ (ProjectiveSpace.toSpec R (ULift.{u}
      (Fin 2)))) ⨿ pullback (a ≫ (boundaryLineProjection R)) ((z ≫ (chart R 0)) ≫
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    ∃ (hT : IsIntegral T) (hn : Mono nφ) (hd : Mono dφ) (ha : Mono aφ) (hc : Mono cφ),
      let := hT
      let := hn
      let := hd
      let := ha
      let := hc
      let := functionalNormProductUnitDomain_nonempty F (dualLineBundle _ c.N)
        (dualLineBundle _ c.N) nφ dφ L L aφ cφ
      ∃ (r : Γ(T, W)) (β : E ⟶ W.toScheme),
        β ≫ W.ι = Hom.normFullBoundaryMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
          (boundaryLineProjection R)) dA (z ≫ (chart R 0)) ∧ IsUnit r ∧
        T.germToFunctionField W r = genericFiberLineRatioNorm (𝟙 T) L aφ cφ *
          genericFiberLineRatioNorm F (dualLineBundle _ c.N) nφ dφ ∧
        (Hom.normFullBoundaryMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
          (boundaryLineProjection R)) dA (z ≫ (chart R 0))).app W r = 1 := by
  let τ := Hom.retainedNormParameterMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
    (boundaryLineProjection R)) (chart R 0) a
    (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
  let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (ProjectiveSpace.toSpec
    R (ULift.{u} (Fin 2))) (chart R 0)) LA
    (Hom.idealInclusion (Hom.compactificationGraph (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
      (chart R 0))) bA
  obtain ⟨_, _, hn, hd'⟩ := BoundarySectionData.global_mono (boundaryLineProjection R) (f ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) j p hq a z s hs H e ha d hd c v hcover
  let := hn
  let := hd'
  let := hFa.mono
  let := hFb.mono
  have : Mono (Hom.idealInclusion (Hom.compactificationGraph
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0))) :=
    Hom.idealInclusionMono _
  let := twistedIdealSection_mono _ (Hom.relativeCompactificationGraphLine
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)) LA
    (Hom.idealInclusion (Hom.compactificationGraph (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
      (chart R 0))) bA
  have hma : Mono (pullbackUnitMap τ (sectionDualFunctional _ M aA)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  have hmc : Mono (pullbackUnitMap τ (sectionDualFunctional _ M cA)) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  let hT := (nativeCorrectionParameter_normal R a).1
  let := hT
  let := hma
  let := hmc
  let := c.n_unit
  let := c.d_unit
  have H0 : IsPullback s (𝟙 Z) (j ≫ f) (z ≫ (chart R 0)) := by
    rw [hret]
    exact Scheme.marked_isPullback_comp_mono p z s H (chart R 0)
  have hcharts : ∀ x : (ProjectiveSpace R (ULift.{u} (Fin 2))), ∃ i, x ∈ Set.range (chart R i) :=
    by
    intro x
    have hx : x ∈ (⨆ i, (chart R i).opensRange) := by
      rw [iSup_chart_opensRange]
      trivial
    exact Opens.mem_iSup.mp hx
  refine ⟨hT, hn, hd', hma, hmc, ?_⟩
  exact exists_originalCorrectionNormalizedUnit (boundaryLineProjection R)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) f j (chart R 0) p hq hret (chart_toSpec R 0)
    a z s hs hsK e ha d bE hbE c.N c.nS c.dS c.hN dA hdA LA aA bA hpairA H0
    bI hbI (fun _ : ULift.{u} (Fin 2) => CommRingCat.of (Polynomial R))
    (chart R) hcharts hfree

end AlgebraicGeometry.Scheme.RelativeCurvePencil
