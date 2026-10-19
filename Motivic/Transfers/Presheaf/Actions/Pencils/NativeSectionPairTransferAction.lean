/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.NativeSectionPairNormalizedUnit
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterGenericRatio
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFreeCharts
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeCorrectionNormAction
/-! # The same original section pair acts identically on every native component

The component geometry and original localized free charts are retained from the
one section choice. The native caller constructs its normalized unit internally.
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

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}} [IsAffine Y]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]
  (i : (nativeSectionPairParameterComponentCover R p O V).I₀)

/-- Normality of every actual affine component-parameter chart comes from the
same original normalization, not from integrality of the whole original source. -/
theorem nativeSectionPairComponent_normal_sections
    (b : (nativeSectionPairParameterComponentCover R p O V).X i ⟶ Spec Γ(V.toScheme, ⊤))
    (W : (pullback b (ProjectiveSpace.toSpec Γ(V.toScheme, ⊤)
      (ULift.{u} (Fin 2)))).Opens) (hW : IsAffineOpen W) (hne : Nonempty W) :
    IsIntegrallyClosed Γ(pullback b (ProjectiveSpace.toSpec Γ(V.toScheme, ⊤)
      (ULift.{u} (Fin 2))), W) := by
  let T := pullback b (ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)))
  have h := nativeSectionPairParameterComponent_product_normal R p O V i Γ(V.toScheme, ⊤) b
  let : IsIntegral T := h.1
  let (x : T) : IsIntegrallyClosed (T.presheaf.stalk x) := h.2.2 x
  let := hne
  exact T.isIntegrallyClosed_sections_of_isAffineOpen W hW

/-- Direct norm charts for the exact twice-restricted original finite map are
free by the retained localization witness, with no new shrink or chart premise. -/
theorem nativeSectionPairComponent_original_free_charts
    (r : R) (hOr : O ≤ PrimeSpectrum.basicOpen r)
    (hfree : ∀ k : ULift.{u} (Fin 2),
      let w := chart (Localization.Away r) k ≫
        ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2))
      let : Algebra (Polynomial (Localization.Away r))
          Γ(pullback (toProjectiveLine R p) w, ⊤) :=
        (scalarMap (pullback.snd (toProjectiveLine R p) w)).toAlgebra
      Module.Free (Polynomial (Localization.Away r))
        Γ(pullback (toProjectiveLine R p) w, ⊤))
    (b : (nativeSectionPairParameterComponentCover R p O V).X i ⟶ Spec Γ(V.toScheme, ⊤)) :
    let F₁ := boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O
    let F₂ := boundaryBaseProjectiveMap Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) F₁ V
    let π := ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2))
    ∀ x : (pullback b π : Scheme.{u}), ∃ (W : (pullback b π).Opens) (hW : IsAffineOpen W), x ∈ W ∧
      (let : Algebra Γ((pullback b π : Scheme.{u}), W)
          Γ(pullback (normProductMap π F₂ b) hW.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (normProductMap π F₂ b) hW.fromSpec)).toAlgebra
       Module.Free Γ((pullback b π : Scheme.{u}), W)
         Γ(pullback (normProductMap π F₂ b) hW.fromSpec, ⊤)) := by
  dsimp only
  intro x
  refine normProductMap_exists_free_affine_neighborhood _ _ b
    (fun _ : ULift.{u} (Fin 2) => CommRingCat.of (Polynomial Γ(V.toScheme, ⊤)))
    (chart Γ(V.toScheme, ⊤)) ?_ ?_ x
  · intro y
    have hy : y ∈ (⨆ k, (chart Γ(V.toScheme, ⊤) k).opensRange) := by
      rw [iSup_chart_opensRange]
      trivial
    exact Opens.mem_iSup.mp hy
  · exact finalCoefficient_chart_sections_free R r O hOr V (toProjectiveLine R p) hfree

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The literal inverse-image boundary used by R3 is nonempty on a genuine
component, via the same infinity product and its canonical Cartesian map. -/
theorem nativeSectionPairBoundary_nonempty
    (R : Type u) [CommRing R] {K D Z : Scheme.{u}} [Nonempty K]
    (b : K ⟶ Spec (.of R)) (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (z : Z ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (hinfty : (Set.range (chart R 0))ᶜ ⊆ Set.range d) :
    Nonempty ((pullback d (pullback.snd b (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ⨿
      pullback z (pullback.snd b (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))) :
        Scheme.{u}) := by
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  have hE := normFullBoundarySource_nonempty_of_cover R b d z hinfty
  let l : pullback b (d ≫ π) ⟶ pullback d (pullback.snd b π) :=
    pullback.lift (pullback.snd b (d ≫ π)) (retainedProductInclusion b π d)
      (retainedProductInclusion_snd b π d).symm
  let r : pullback b (z ≫ π) ⟶ pullback z (pullback.snd b π) :=
    pullback.lift (pullback.snd b (z ≫ π)) (retainedProductInclusion b π z)
      (retainedProductInclusion_snd b π z).symm
  exact ⟨(coprod.map l r) (Classical.choice hE)⟩

/-- The actual small retained complement is covered by the literal R3 boundary;
this is only a support statement and does not replace its scheme-level value. -/
theorem nativeSectionPairBoundary_covers_complement
    {S P X K D Z A : Scheme.{u}} (π : P ⟶ S) (b : K ⟶ S)
    (j : X ⟶ P) (a : A ⟶ X) (d : D ⟶ P) (z : Z ⟶ X)
    (hinfty : (Set.range j)ᶜ ⊆ Set.range d)
    (hpuncture : (Set.range a)ᶜ ⊆ Set.range z) :
    (Set.range (retainedProductInclusion b π (a ≫ j)))ᶜ ⊆
      Set.range (sectionPairParameterBoundary (pullback.snd b π) d (z ≫ j)) := by
  rw [sectionPairParameterBoundary_range, ← range_normFullBoundaryMap]
  exact correctionNorm_retained_complement_subset_fullBoundary π b j a d z hinfty hpuncture

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace Motivic.PresheafWithTransfers
open Scheme.RelativeCurvePencil

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

local instance nativeSectionPair_small_smooth
    (R : Type u) [CommRing R] {A : Scheme.{u}}
    (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a]
    [SmoothOfRelativeDimension 1 ((chart R 0) ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))] :
    SmoothOfRelativeDimension 1 ((a ≫ chart R 0) ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

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
theorem exists_nativeSectionPairPrincipalAction_zero
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
  dsimp only
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
  let b := α ≫ j ≫ f ≫ π
  let T := pullback b π
  let ρ := nativeSectionPairParameterComponentProductMap R₀ p₀ O₀ V₀ i R (j ≫ f ≫ π)
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
  obtain ⟨hT, haB, hcB, haA, hcA, hW, r, eW, heW, hr, hg, he⟩ :=
    exists_nativeSectionPairNormalizedUnit R₀ p₀ O₀ V₀ R f j p hq hret
      a z s hs H hsK e ha d hd c v hcover dA hdA bI hbI bE hbE
      LA aA bA iA hFa hFb hpairA i hfree
  let := hT
  let := haB
  let := hcB
  let := haA
  let := hcA
  let := hW
  let hTN := (nativeSectionPairParameterComponent_product_normal R₀ p₀ O₀ V₀ i R b).2.1
  let := hTN
  let : IsLocallyNoetherian (retainedProduct b π (a ≫ chart R 0)) :=
    LocallyOfFiniteType.isLocallyNoetherian jT
  let : IsNoetherian (retainedProduct b π (a ≫ chart R 0)) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hρ : ρ ≫ pullback.snd (j ≫ f ≫ π) π = pullback.snd b π := by
    exact constantSourceMapOfEq_snd α (j ≫ f ≫ π) π b rfl
  have hCov : (Set.range jT)ᶜ ⊆ Set.range (eW ≫ W.ι) := by
    rw [heW]
    change (Set.range jT)ᶜ ⊆ Set.range
      (sectionPairParameterBoundary (ρ ≫ pullback.snd (j ≫ f ≫ π) π) dA (z ≫ chart R 0))
    rw [hρ]
    exact nativeSectionPairBoundary_covers_complement π b (chart R 0) a dA z hinfty hpuncture
  have hbase : jT ≫ pullback.fst b π ≫ X.hom = g ≫ Q.hom := by
    change jT ≫ pullback.fst b π ≫ (b ≫ t) = g ≫ (((a ≫ chart R 0) ≫ π) ≫ t)
    simpa only [Category.assoc] using retainedProduct_structure b π (a ≫ chart R 0) t
  have hNE : Nonempty (pullback dA (ρ ≫ pullback.snd (j ≫ f ≫ π) π) ⨿
      pullback (z ≫ chart R 0) (ρ ≫ pullback.snd (j ≫ f ≫ π) π) : Scheme.{u}) := by
    rw [hρ]
    exact nativeSectionPairBoundary_nonempty R b dA (z ≫ chart R 0) hinfty
  let := hNE
  have heTop : eW.appTop (W.topIso.inv r) = 1 :=
    appTop_eq_one_of_open_factor E W r eW heW he
  refine ⟨hT, hTN, haB, hcB, haA, hcA, hW, r, eW, heW, hr, hCov, hbase, hg, he, ?_⟩
  exact transfer_principalOrder_open_eq_zero Pst hPst X Q (pullback.fst b π)
    jT W r hr eW hCov heTop g hbase

end Motivic.PresheafWithTransfers
