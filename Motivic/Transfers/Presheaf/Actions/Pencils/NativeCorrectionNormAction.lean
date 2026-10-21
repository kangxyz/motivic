/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NativeCorrectionNormalizedUnit
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NormBoundaryCover
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.NormNonempty
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.BoundarySections
public import Motivic.Transfers.Presheaf.Actions.Principal.Open
/-! # Principal action of the same original correction norm product

The original sections construct the good open, unit and original-product germ.
The actual full boundary supplies its nonemptiness, omitted-locus coverage and
value one. The resulting principal correspondence acts by zero on an ordinary
HI presheaf with transfers. The smaller retained target is independent of the
original marked source neighborhood used in normalization.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.Hom Scheme.RelativeCurvePencil
open RelativeProjectiveLine
universe v u

namespace AlgebraicGeometry.RelativeProjectiveLine

/-- Any actual infinity boundary covering the omitted affine chart is nonempty
after base change by a nonempty parameter. No scheme structure is replaced. -/
theorem normFullBoundarySource_nonempty_of_cover
    (R : Type u) [CommRing R] {A D Z : Scheme.{u}} [Nonempty A]
    (a : A ⟶ Spec (.of R)) (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (z : Z ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (hinfty : (Set.range (chart R 0))ᶜ ⊆ Set.range d) :
    Nonempty ((pullback a (d ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⨿
      pullback a (z ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) : Scheme.{u}) := by
  let x : A := Classical.choice inferInstance
  obtain ⟨b, hb⟩ := neighborhoodBoundary_toSpec_surjective R ⊤ (a x)
  have hi : neighborhoodBoundaryInclusion R ⊤ b ∉ Set.range (chart R 0) := by
    have hm : neighborhoodBoundaryInclusion R ⊤ b ∈
        Set.range (neighborhoodBoundaryInclusion R ⊤) := ⟨b, rfl⟩
    rw [range_neighborhoodBoundaryInclusion] at hm
    rintro ⟨y, hy⟩
    exact hm ⟨y, trivial, hy⟩
  obtain ⟨b', hb'⟩ := hinfty hi
  have he : a x = (d ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) b' := by
    simpa only [Scheme.Hom.comp_apply, hb'] using hb.symm
  obtain ⟨y, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x b' he
  exact ⟨(coprod.inl : pullback a (d ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⟶
    pullback a (d ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⨿
      pullback a (z ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) y⟩

end AlgebraicGeometry.RelativeProjectiveLine

namespace Motivic.PresheafWithTransfers

/-- The smoothness instance used in this module. -/
local instance nativeCorrectionNormActionSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

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

variable {k : Type u} [Field k] (Pst : PresheafWithTransfers.{v} k)
  (hPst : Pst.IsA1Invariant) (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (Q : SmoothSite (Spec (.of k)))
  {U : Scheme.{u}} [IsAffine U] (v₁ : U ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsOpenImmersion
    v₁]
  [SmoothOfRelativeDimension 1 ((v₁ ≫ (chart R 0)) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2))))]
  (hinfty : (Set.range (chart R 0))ᶜ ⊆ Set.range dA)
  (hpuncture : (Set.range v₁)ᶜ ⊆ Set.range z)
  (g : retainedProduct (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2))) (v₁ ≫ (chart R 0)) ⟶ Q.left)
  (hbase : retainedProductInclusion (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R
    (ULift.{u} (Fin 2))) (v₁ ≫ (chart R 0)) ≫
    pullback.fst (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ≫
      (psiSourceSite k t (boundaryLineProjection R) a).hom = g ≫ Q.hom)

include hret hcover hbI hbE hFa hFb hpairA hPst hinfty hpuncture hbase in
/-- The original R5 has zero principal action on the actual small retained
curve. Neither its good open, unit, generic germ nor boundary value is assumed.
The full original boundary remains unchanged, including every nilpotent. -/
theorem exists_nativeCorrectionPrincipalAction_zero
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (chart R i))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R i), ⊤)) :
    let T :=
      pullback (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
    let F :=
      normProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) f (a ≫ (boundaryLineProjection
        R))
    let τ :=
      retainedNormParameterMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
        (boundaryLineProjection R)) (chart R 0) a
        (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
    let M :=
      tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine
        (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))
    let cA :=
      twistedIdealSection _ (relativeCompactificationGraphLine (ProjectiveSpace.toSpec R
        (ULift.{u} (Fin 2))) (chart R 0)) LA
        (idealInclusion (compactificationGraph
          (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0))) bA
    let L := pullbackLineBundle τ (dualLineBundle _ M)
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
    let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
    let W := functionalNormProductUnitDomain F (dualLineBundle _ c.N)
      (dualLineBundle _ c.N) nφ dφ L L aφ cφ
    let E :=
      pullback (a ≫ (boundaryLineProjection R)) (dA ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
        2)))) ⨿ pullback (a ≫ (boundaryLineProjection R)) ((z ≫ (chart R 0)) ≫
        (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    let jT :=
      retainedProductInclusion (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R
        (ULift.{u} (Fin 2))) (v₁ ≫ (chart R 0))
    let : IsAffine (psiSourceSite k t (boundaryLineProjection R) a).left := ‹IsAffine A›
    let : IsAffine (retainedProduct (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R
      (ULift.{u} (Fin 2))) (v₁ ≫ (chart R 0))) :=
      retainedProduct_affine (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u}
        (Fin 2))) (v₁ ≫ (chart R 0))
    let : SmoothOfRelativeDimension 1 (jT ≫ pullback.fst (a ≫ (boundaryLineProjection R))
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) :=
      retainedProduct_smooth (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u}
        (Fin 2))) (v₁ ≫ (chart R 0))
    ∃ (hT : IsIntegral T) (hTN : IsNoetherian T)
      (hn : Mono nφ) (hd : Mono dφ) (haφ : Mono aφ) (hcφ : Mono cφ),
      let := hT
      let := hTN
      let := hn
      let := hd
      let := haφ
      let := hcφ
      let := functionalNormProductUnitDomain_nonempty F (dualLineBundle _ c.N)
        (dualLineBundle _ c.N) nφ dφ L L aφ cφ
      ∃ (r : Γ(T, W)) (β : E ⟶ W.toScheme)
        (_hβ : β ≫ W.ι = normFullBoundaryMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
          (boundaryLineProjection R)) dA (z ≫ (chart R 0)))
        (hr : IsUnit r) (hboundary : (Set.range jT)ᶜ ⊆ Set.range (β ≫ W.ι)),
        T.germToFunctionField W r = genericFiberLineRatioNorm (𝟙 T) L aφ cφ *
          genericFiberLineRatioNorm F (dualLineBundle _ c.N) nφ dφ ∧
        (normFullBoundaryMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
          (boundaryLineProjection R)) dA (z ≫ (chart R 0))).app W r = 1 ∧
        Pst.transfer (PrincipalOrderCorrespondence.correspondence
          (X := psiSourceSite k t (boundaryLineProjection R) a) (Y := Q)
          (pullback.fst (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
            2)))) jT W
          (PrincipalOrderCorrespondence.canonical_boundary_cover jT W β hboundary)
          r hr g hbase) = 0 := by
  let T := pullback (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  let F :=
    normProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) f (a ≫ (boundaryLineProjection R))
  let τ :=
    retainedNormParameterMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (a ≫
      (boundaryLineProjection R)) (chart R 0) a
      (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
  let M :=
    tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))
  let cA :=
    twistedIdealSection _ (relativeCompactificationGraphLine (ProjectiveSpace.toSpec R (ULift.{u}
      (Fin 2))) (chart R 0)) LA
      (idealInclusion (compactificationGraph
        (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0))) bA
  let L := pullbackLineBundle τ (dualLineBundle _ M)
  let nφ := sectionDualFunctional _ c.N c.nS
  let dφ := sectionDualFunctional _ c.N c.dS
  let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
  let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
  let W := functionalNormProductUnitDomain F (dualLineBundle _ c.N)
    (dualLineBundle _ c.N) nφ dφ L L aφ cφ
  let E :=
    pullback (a ≫ (boundaryLineProjection R)) (dA ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
      2)))) ⨿ pullback (a ≫ (boundaryLineProjection R)) ((z ≫ (chart R 0)) ≫
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
  let jT :=
    retainedProductInclusion (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u}
      (Fin 2))) (v₁ ≫ (chart R 0))
  let : IsAffine (psiSourceSite k t (boundaryLineProjection R) a).left := ‹IsAffine A›
  let : IsAffine (retainedProduct (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R
    (ULift.{u} (Fin 2))) (v₁ ≫ (chart R 0))) :=
    retainedProduct_affine (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u}
      (Fin 2))) (v₁ ≫ (chart R 0))
  let : SmoothOfRelativeDimension 1 (jT ≫ pullback.fst (a ≫ (boundaryLineProjection R))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) :=
    retainedProduct_smooth (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u}
      (Fin 2))) (v₁ ≫ (chart R 0))
  obtain ⟨hT, hn, hd', haφ, hcφ, r, β, hβ, hr, hg, hb⟩ :=
    exists_nativeCorrectionNormalizedUnit R f j p hq hret a z s hs H hsK e ha
      d hd c v hcover dA hdA bI hbI bE hbE LA aA bA iA hFa hFb hpairA hfree
  let := hT
  let := hn
  let := hd'
  let := haφ
  let := hcφ
  let hTN := (nativeCorrectionParameter_normal R a).2.1
  let := hTN
  let : IsIntegral A := isIntegral_of_isOpenImmersion a
  let : IsIntegral (psiSourceSite k t (boundaryLineProjection R) a).left := ‹IsIntegral A›
  let : Nonempty W := functionalNormProductUnitDomain_nonempty F (dualLineBundle _ c.N)
    (dualLineBundle _ c.N) nφ dφ L L aφ cφ
  let : IsLocallyNoetherian (retainedProduct (a ≫ (boundaryLineProjection R))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (v₁ ≫ (chart R 0))) :=
    LocallyOfFiniteType.isLocallyNoetherian jT
  let : IsNoetherian (retainedProduct (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R
    (ULift.{u} (Fin 2))) (v₁ ≫ (chart R 0))) :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  let : Nonempty E := normFullBoundarySource_nonempty_of_cover R
    (a ≫ (boundaryLineProjection R)) dA (z ≫ (chart R 0)) hinfty
  have hboundary : (Set.range jT)ᶜ ⊆ Set.range (β ≫ W.ι) := by
    rw [hβ]
    exact correctionNorm_retained_complement_subset_fullBoundary (ProjectiveSpace.toSpec R
      (ULift.{u} (Fin 2))) (a ≫ (boundaryLineProjection R))
      (chart R 0) v₁ dA z hinfty hpuncture
  have hbTop : β.appTop (W.topIso.inv r) = 1 :=
    appTop_eq_one_of_open_factor (normFullBoundaryMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin
      2))) (a ≫ (boundaryLineProjection R)) dA (z ≫ (chart R 0)))
      W r β hβ hb
  refine ⟨hT, hTN, hn, hd', haφ, hcφ, r, β, hβ, hr, hboundary, hg, hb, ?_⟩
  exact transfer_principalOrder_open_eq_zero Pst hPst (psiSourceSite k t (boundaryLineProjection
    R) a) Q
    (pullback.fst (a ≫ (boundaryLineProjection R)) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
      jT W r hr β hboundary hbTop g hbase

end Motivic.PresheafWithTransfers
