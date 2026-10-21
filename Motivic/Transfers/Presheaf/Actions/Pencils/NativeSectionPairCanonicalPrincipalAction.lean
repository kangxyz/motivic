/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairPrincipalPresentation
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.NativeSectionPairNormalizedUnit
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterGenericRatio
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFreeCharts
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeCorrectionNormAction


/-! # Actual native principal witness in the canonical Cor presentation

This diagnostic obtains the original native tuple once and transports only its
principal zero action through the checked same-data presentation equality.
It is not a proof of the final E3 lambda action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible RelativeProjectiveLine
open Scheme.RelativeAffineLineEtaleCompactification
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u w

namespace Motivic.PresheafWithTransfers
open Scheme.RelativeCurvePencil

attribute [local instance] Cor.nativeOriginalPairTransferActionSmooth

attribute [local instance] nativeSectionPair_small_smooth

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


variable {k : Type u} [Field k] (Pst : PresheafWithTransfers.{w} k)
  (hPst : Pst.IsA1Invariant) (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (hinfty : (Set.range (chart R 0))ᶜ ⊆ Set.range dA)
  (hpuncture : (Set.range a)ᶜ ⊆ Set.range z)

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] in
include hret hcover hbI hbE hFa hFb hpairA hPst hinfty hpuncture in
/-- The actual R3 on a genuine original component has zero principal action.
The unit, its full boundary factor and its native norm germ are constructed
internally from the same source and target section choices. -/
theorem exists_nativeSectionPairPrincipalAction_zero_canonical
    (i : (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).I₀)
    (hfree : ∀ k : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R k), ⊤) :=
        (scalarMap (pullback.snd f (chart R k))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R k), ⊤)) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
    let b := α ≫ j ≫ f ≫ π
    let T := pullback b π
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
    let W := sectionPairNormParameterUnitDomain π f j (chart R 0) p hret
      LA aA bA c.T c.aS c.bS ρ
    let E := sectionPairParameterBoundary (ρ ≫ pullback.snd (j ≫ f ≫ π) π) dA
      (z ≫ chart R 0)
    let X := relativeCommonSite k t (f ≫ π) j α
    let Q := relativeTargetSite k t π (a ≫ chart R 0)
    let jT := retainedProductInclusion b π (a ≫ chart R 0)
    let g := pullback.snd b ((a ≫ chart R 0) ≫ π)
    let : IsAffine X.left :=
      inferInstanceAs (IsAffine ((nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).X i))
    let : IsIntegral X.left :=
      inferInstanceAs (IsIntegral ((nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).X i))
    let : IsAffine (retainedProduct b π (a ≫ chart R 0)) :=
      retainedProduct_affine b π (a ≫ chart R 0)
    let : SmoothOfRelativeDimension 1 (jT ≫ pullback.fst b π) :=
      retainedProduct_smooth b π (a ≫ chart R 0)
    ∃ (hT : IsIntegral T) (hTN : IsNoetherian T)
      (haB : Mono afB) (hcB : Mono cfB) (haA : Mono afA) (hcA : Mono cfA),
      let := hT
      let := hTN
      let := haB
      let := hcB
      let := haA
      let := hcA
      ∃ (hW : Nonempty W) (r : Γ(T, W)) (eW : _ ⟶ W.toScheme),
        let := hW
        ∃ (_heW : eW ≫ W.ι = E) (hr : IsUnit r)
          (hCov : (Set.range jT)ᶜ ⊆ Set.range (eW ≫ W.ι))
          (hbase : jT ≫ pullback.fst b π ≫ X.hom = g ≫ Q.hom),
          T.germToFunctionField W r =
            genericFiberLineRatioNorm (pullback.snd F ρ)
              (pullbackLineBundle (pullback.fst F ρ) (dualLineBundle _ MB)) afB cfB /
            genericFiberLineRatioNorm (𝟙 T)
              (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA ∧
          E.app W r = 1 ∧
          Pst.transfer (PrincipalOrderCorrespondence.correspondence
            (X := X) (Y := Q) (pullback.fst b π) jT W
            (PrincipalOrderCorrespondence.canonical_boundary_cover jT W eW hCov)
            r hr g hbase) = 0 := by
  intro π α b T ρ F κ MA MB cA cB afB cfB afA cfA W E X Q jT g
    hAffineX hIntegralX hAffineRetained hSmoothRetained
  obtain ⟨hT, hTN, haB, hcB, haA, hcA, hW, r, eW, heW, hr, hCov,
      hbase, hg, he, hzero⟩ :=
    exists_nativeSectionPairPrincipalAction_zero R₀ p₀ O₀ V₀ R f j p hq hret
      a z s hs H hsK e ha d hd c v hcover dA hdA bI hbI bE hbE
      LA aA bA iA hFa hFb hpairA Pst hPst t hinfty hpuncture i hfree
  let := hT
  let := hTN
  let := haB
  let := hcB
  let := haA
  let := hcA
  let := hW
  have hPrincipal := sectionPair_principal_native_eq_canonical
    (t := t) (π := π) (f := f) (j := j) (α := α)
    (jA := chart R 0) (a := a) W r hr
    (PrincipalOrderCorrespondence.canonical_boundary_cover jT W eW hCov)
    (PrincipalOrderCorrespondence.canonical_boundary_cover jT W eW hCov)
    hbase hbase
  have hzeroCanonical := (congrArg
    (fun z : Cor.mk X ⟶ Cor.mk Q => Pst.transfer z) hPrincipal).symm.trans hzero
  exact ⟨hT, hTN, haB, hcB, haA, hcA, hW, r, eW, heW, hr, hCov,
    hbase, hg, he, hzeroCanonical⟩

end Motivic.PresheafWithTransfers
