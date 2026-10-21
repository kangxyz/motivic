/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairCanonicalPrincipalAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalComponentLambdaDifference
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalTargetLambda
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterTargetMap

/-! # Native specialization of the original E3 correspondence

The same native normalized section and its Cartesian generic germ determine the
actual original correspondence difference. Normality, free charts, and the
change to the direct finite norm presentation are supplied internally. This
leaf is independent of a presheaf and does not assume any desired relation.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible RelativeProjectiveLine
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u w

namespace AlgebraicGeometry.Scheme

/-- Equal actual target maps give the same identity-norm ratio for the same
original line and functionals, including all pullback-module identifications. -/
theorem genericFiberLineRatioNorm_id_pullback_congr
    {T B : Scheme.{u}} [IsIntegral T] (v w : T ⟶ B) (h : v = w)
    (L : LineBundle B) (a c : L.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    [Mono (pullbackUnitMap v a)] [Mono (pullbackUnitMap v c)]
    [Mono (pullbackUnitMap w a)] [Mono (pullbackUnitMap w c)] :
    genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle v L)
        (pullbackUnitMap v a) (pullbackUnitMap v c) =
      genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle w L)
        (pullbackUnitMap w a) (pullbackUnitMap w c) := by
  subst w
  rfl

section ParameterRatio
variable {S C P Y X K : Scheme.{u}}
  (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
  (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X)
  (hret : jB ≫ f = p ≫ jA) (α : K ⟶ Y)

local notation "q" => (jB ≫ f ≫ π)
local notation "b" => (α ≫ q)
local notation "T" => (pullback b π : Scheme)
local notation "ρ" => (constantSourceMapOfEq α q π b rfl)
local notation "F" => (normProductMap π f q)
local notation "κ" => (ρ ≫ retainedParameterProductMap π f jB jA p hret)
local notation "sMap" => (constantSourceMapOfEq α q (f ≫ π) b rfl)
local notation "tMap" => (retainedNormParameterMap π b jA (α ≫ p)
  (originalNormPairComponentBase_eq π f jB α jA p hret))

/-- The actual Cartesian parameter presentation and direct product presentation
have the same norm quotient of the unchanged original functionals. -/
theorem sectionPairParameter_genericRatio_coherence
    [IsIntegral T]
    (LB : LineBundle (pullback q (f ≫ π)))
    (aB cB : LB.val ⟶ SheafOfModules.unit (pullback q (f ≫ π)).ringCatSheaf)
    (LA : LineBundle (pullback (jA ≫ π) π))
    (aA cA : LA.val ⟶ SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf)
    [Mono (pullbackUnitMap (pullback.fst F ρ) aB)]
    [Mono (pullbackUnitMap (pullback.fst F ρ) cB)]
    [Mono (pullbackUnitMap sMap aB)] [Mono (pullbackUnitMap sMap cB)]
    [Mono (pullbackUnitMap κ aA)] [Mono (pullbackUnitMap κ cA)]
    [Mono (pullbackUnitMap tMap aA)] [Mono (pullbackUnitMap tMap cA)] :
    genericFiberLineRatioNorm (pullback.snd F ρ)
        (pullbackLineBundle (pullback.fst F ρ) LB)
        (pullbackUnitMap (pullback.fst F ρ) aB)
        (pullbackUnitMap (pullback.fst F ρ) cB) /
      genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ LA)
        (pullbackUnitMap κ aA) (pullbackUnitMap κ cA) =
    genericFiberLineRatioNorm (normProductMap π f b) (pullbackLineBundle sMap LB)
        (pullbackUnitMap sMap aB) (pullbackUnitMap sMap cB) /
      genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle tMap LA)
        (pullbackUnitMap tMap aA) (pullbackUnitMap tMap cA) := by
  apply congrArg₂ (fun x y => x / y)
  · exact (normProductParameter_genericRatio_eq π f q α b rfl LB aB cB).symm
  · exact genericFiberLineRatioNorm_id_pullback_congr κ tMap
      (originalNormParameter_target_comp π f jB jA p hret α b rfl
        (originalNormPairComponentBase_eq π f jB α jA p hret)) LA aA cA

end ParameterRatio

end AlgebraicGeometry.Scheme

namespace Motivic.PresheafWithTransfers
open Motivic.Cor

attribute [local instance] Cor.instSmoothOfSmoothOfRelativeDimensionOfNatNat

variable (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀] {Y₀ : Scheme.{u}} [IsAffine Y₀]
  (p₀ : Y₀ ⟶ Spec (.of (Polynomial R₀))) [Etale p₀] [QuasiCompact p₀] [IsSeparated p₀]
  (O₀ : (Spec (.of R₀)).Opens) [IsAffine O₀.toScheme]
  (V₀ : (Spec Γ(O₀.toScheme, ⊤)).Opens) [IsAffine V₀.toScheme]

variable (R : Type u) [CommRing R]

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
  (e : SheafOfModules.unit (pullback (boundaryLineProjection R) (z ≫ (boundaryLineProjection
    R))).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget (boundaryLineProjection R) z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (c : BoundarySectionData (boundaryLineProjection R) (f ≫ (ProjectiveSpace.toSpec R (ULift.{u}
    (Fin 2)))) j p hq a z s hs H e ha d hd)
  (vB : V ⟶ finalOriginalSource R₀ p₀ O₀ V₀) [IsOpenImmersion vB]
  (vA : V ⟶ A) (hsmall : vB ≫ p = vA ≫ a)
  [SmoothOfRelativeDimension 1 ((vB ≫ j) ≫
    (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]
  (hcover : ∀ x : C, x ∈ Set.range (vB ≫ j) ∨ x ∈ Set.range d ∨
    x ∈ Set.range (s ≫ j))
  {DA : Scheme.{u}} (dA : DA ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))) [IsAffineHom dA]
  (hdA : Disjoint (Set.range (chart R 0)) (Set.range dA))
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


variable {B : Scheme.{u}} [IsAffine B]
  (αorig : B ⟶ finalOriginalSource R₀ p₀ O₀ V₀) [Smooth αorig]
  (βorig : B ⟶ A) [Flat βorig] (horig : αorig ≫ p = βorig ≫ a)
  (φorig : B ⟶ V) (hφorig : φorig ≫ (vB ≫ j) = αorig ≫ j)
  (hcoverA : ∀ x : ProjectiveSpace R (ULift.{u} (Fin 2)),
    x ∈ Set.range (a ≫ chart R 0) ∨ x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ chart R 0))
  {k : Type u} [Field k]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]

/-- The relative-dimension instance used in this module. -/
local instance nativeSectionPairCorSpecializationSmoothRelativeDimension
    : SmoothOfRelativeDimension 1 ((a ≫ chart R 0) ≫
    ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

omit [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] in
include hret hcover hFa hFb hpairA hsmall hcoverA in
/-- Native geometry specializes the original correspondence theorem to the same
normalized unit and Cartesian generic germ, without a desired-relation input. -/
theorem nativeSectionPair_originalLambda_eq_principal
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
    let _κA := retainedNormParameterMap π b (chart R 0) (α ≫ p)
      (originalNormPairComponentBase_eq π f j α (chart R 0) p hret)
    let _κB := constantSourceMapOfEq α (j ≫ f ≫ π) (f ≫ π) b rfl
    let MA := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π
      (chart R 0)))
    let MB := tensorLineBundle _ c.T (dualLineBundle _
      (relativeCompactificationGraphLine (f ≫ π) j))
    let afB := sectionDualFunctional _ MB c.aS
    let cfB := sectionDualFunctional _ MB
      (twistedIdealSection _ (relativeCompactificationGraphLine (f ≫ π) j) c.T
        (idealInclusion (compactificationGraph (f ≫ π) j)) c.bS)
    let afA := sectionDualFunctional _ MA aA
    let cfA := sectionDualFunctional _ MA
      (twistedIdealSection _ (relativeCompactificationGraphLine π (chart R 0)) LA
        (idealInclusion (compactificationGraph π (chart R 0))) bA)
    let W := sectionPairNormParameterUnitDomain π f j (chart R 0) p hret
      LA aA bA c.T c.aS c.bS ρ
    ∀ (hT : IsIntegral T) (hTN : IsNoetherian T),
    let := hT
    let := hTN
    ∀ (haB : Mono (pullbackUnitMap
        (pullback.fst (normProductMap π f (j ≫ f ≫ π)) ρ) afB))
      (hcB : Mono (pullbackUnitMap
        (pullback.fst (normProductMap π f (j ≫ f ≫ π)) ρ) cfB))
      (haA : Mono (pullbackUnitMap
        (ρ ≫ retainedParameterProductMap π f j (chart R 0) p hret) afA))
      (hcA : Mono (pullbackUnitMap
        (ρ ≫ retainedParameterProductMap π f j (chart R 0) p hret) cfA)),
    let := haB
    let := hcB
    let := haA
    let := hcA
    ∀ (hW : Nonempty W),
    let := hW
    ∀ (r : Γ(T, W)) (hr : IsUnit r)
      (eW : pullback dA (ρ ≫ pullback.snd (j ≫ f ≫ π) π) ⨿
        pullback (z ≫ chart R 0) (ρ ≫ pullback.snd (j ≫ f ≫ π) π) ⟶ W.toScheme)
      (hCov : (Set.range (retainedProductInclusion b π (a ≫ chart R 0)))ᶜ ⊆
        Set.range (eW ≫ W.ι)),
    T.germToFunctionField W r =
      genericFiberLineRatioNorm
        (pullback.snd (normProductMap π f (j ≫ f ≫ π)) ρ)
        (pullbackLineBundle (pullback.fst (normProductMap π f (j ≫ f ≫ π)) ρ)
          (dualLineBundle _ MB))
        (pullbackUnitMap (pullback.fst (normProductMap π f (j ≫ f ≫ π)) ρ) afB)
        (pullbackUnitMap (pullback.fst (normProductMap π f (j ≫ f ≫ π)) ρ) cfB) /
      genericFiberLineRatioNorm (𝟙 T)
        (pullbackLineBundle (ρ ≫ retainedParameterProductMap π f j (chart R 0) p hret)
          (dualLineBundle _ MA))
        (pullbackUnitMap (ρ ≫ retainedParameterProductMap π f j (chart R 0) p hret) afA)
        (pullbackUnitMap (ρ ≫ retainedParameterProductMap π f j (chart R 0) p hret) cfA) →
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π (chart R 0) dA z) aA) :=
      inferInstanceAs (IsIso (pullbackSectionMap
        (coprod.desc (infinityProductMap π (chart R 0) dA)
          (graphBoundaryRestriction π (chart R 0) z)) aA))
    let : IsAffine (relativeCommonSite k t (f ≫ π) j α).left :=
      inferInstanceAs (IsAffine ((nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).X i))
    let : IsIntegral (relativeCommonSite k t (f ≫ π) j α).left :=
      inferInstanceAs (IsIntegral ((nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).X i))
    let : IsAffine (retainedProduct b π (a ≫ chart R 0)) :=
      retainedProduct_affine b π (a ≫ chart R 0)
    let : SmoothOfRelativeDimension 1
        (retainedProductInclusion b π (a ≫ chart R 0) ≫ pullback.fst b π) :=
      retainedProduct_smooth b π (a ≫ chart R 0)
    Cor.originalComponentLambdaDifference
      (t := t) (qX := boundaryLineProjection R) (π := π) (F := f) (jB := j)
      (jA := chart R 0) (p := p) (α := α) (hret := hret) (hbase := hq)
      (a := a) (vB := vB) (vA := vA) (hsmall := hsmall)
      (αorig := αorig) (βorig := βorig) (horig := horig)
      (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
      (H := H) (e := e) (ha := ha) (dB := d) (hdB := hd) (dA := dA)
      (hcoverB := hcover) (hcoverA := hcoverA) (source := c)
      (LA := LA) (aA := aA) (bA := bA) =
    PrincipalOrderCorrespondence.correspondence
      (pullback.fst b π) (retainedProductInclusion b π (a ≫ chart R 0)) W
      (PrincipalOrderCorrespondence.canonical_boundary_cover
        (retainedProductInclusion b π (a ≫ chart R 0)) W eW hCov)
      r hr (pullback.snd b ((a ≫ chart R 0) ≫ π))
      (by
        change (retainedProductInclusion b π (a ≫ chart R 0)) ≫
          (pullback.fst b π) ≫ (b ≫ t) =
          (pullback.snd b ((a ≫ chart R 0) ≫ π)) ≫ (((a ≫ chart R 0) ≫ π) ≫ t)
        simpa only [Category.assoc] using retainedProduct_structure b π (a ≫ chart R 0) t) := by
  intro π α b T ρ κA κB MA MB afB cfB afA cfA W hT hTN
    hT' hTN' haB hcB haA hcA haB' hcB' haA' hcA' hW hW' r hr eW hCov hg
    haBoundary hAffineX hIntegralX hAffineRetained hSmoothRetained
  obtain ⟨haB₀, hbB₀, _, _⟩ := BoundarySectionData.global_mono
    (boundaryLineProjection R) (f ≫ π) j p hq a z s hs H e ha d hd c (vB ≫ j) hcover
  let := haB₀
  let := hbB₀
  let := hFa.mono
  let := hFb.mono
  let : Mono (idealInclusion (compactificationGraph (f ≫ π) j)) := idealInclusionMono _
  let : Mono (idealInclusion (compactificationGraph π (chart R 0))) := idealInclusionMono _
  let : Mono cfB := twistedIdealSection_mono _
    (relativeCompactificationGraphLine (f ≫ π) j) c.T
    (idealInclusion (compactificationGraph (f ≫ π) j)) c.bS
  let : Mono cfA := twistedIdealSection_mono _
    (relativeCompactificationGraphLine π (chart R 0)) LA
    (idealInclusion (compactificationGraph π (chart R 0))) bA
  let : Mono (pullbackUnitMap κB afB) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  let : Mono (pullbackUnitMap κB cfB) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  let : Mono (pullbackUnitMap κA afA) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  let : Mono (pullbackUnitMap κA cfA) := by
    dsimp only [pullbackUnitMap, Hom.pullbackToUnit]
    infer_instance
  let : Mono (pullbackUnitMap
      (pullback.fst (normProductMap π f (j ≫ f ≫ π))
        (constantSourceMapOfEq α (j ≫ f ≫ π) π b rfl)) afB) := haB
  let : Mono (pullbackUnitMap
      (pullback.fst (normProductMap π f (j ≫ f ≫ π))
        (constantSourceMapOfEq α (j ≫ f ≫ π) π b rfl)) cfB) := hcB
  let : Mono (pullbackUnitMap
      (constantSourceMapOfEq α (j ≫ f ≫ π) π b rfl ≫
        retainedParameterProductMap π f j (chart R 0) p hret) afA) := haA
  let : Mono (pullbackUnitMap
      (constantSourceMapOfEq α (j ≫ f ≫ π) π b rfl ≫
        retainedParameterProductMap π f j (chart R 0) p hret) cfA) := hcA
  have hgDirect : T.germToFunctionField W r =
      genericFiberLineRatioNorm (normProductMap π f b) (pullbackLineBundle κB
        (dualLineBundle _ MB)) (pullbackUnitMap κB afB) (pullbackUnitMap κB cfB) /
      genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κA (dualLineBundle _ MA))
        (pullbackUnitMap κA afA) (pullbackUnitMap κA cfA) := by
    exact hg.trans (sectionPairParameter_genericRatio_coherence
      π f j (chart R 0) p hret α (dualLineBundle _ MB) afB cfB
      (dualLineBundle _ MA) afA cfA)
  have hnormal : ∀ (U : T.Opens), IsAffineOpen U → Nonempty U →
      IsIntegrallyClosed Γ(T, U) := by
    intro U hU hn
    let (x : T) : IsIntegrallyClosed (T.presheaf.stalk x) :=
      (nativeSectionPairParameterComponent_product_normal R₀ p₀ O₀ V₀ i R b).2.2 x
    let := hn
    exact T.isIntegrallyClosed_sections_of_isAffineOpen U hU
  have hfreeLocal : ∀ x : T, ∃ (U : T.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T, U) Γ(pullback (normProductMap π f b) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (normProductMap π f b) hU.fromSpec)).toAlgebra
       Module.Free Γ(T, U) Γ(pullback (normProductMap π f b) hU.fromSpec, ⊤)) := by
    intro x
    refine normProductMap_exists_free_affine_neighborhood π f b
      (fun _ : ULift.{u} (Fin 2) => CommRingCat.of (Polynomial R)) (chart R) ?_ hfree x
    intro y
    have hy : y ∈ (⨆ k, (chart R k).opensRange) := by
      rw [iSup_chart_opensRange]
      trivial
    exact Opens.mem_iSup.mp hy
  have hWcover := PrincipalOrderCorrespondence.canonical_boundary_cover
    (retainedProductInclusion b π (a ≫ chart R 0)) W eW hCov
  let : IsIso (pullbackSectionMap (fullBoundaryProductMap π (chart R 0) dA z) aA) := by
    change IsIso (pullbackSectionMap (coprod.desc (infinityProductMap π (chart R 0) dA)
      (graphBoundaryRestriction π (chart R 0) z)) aA)
    infer_instance
  have hcor := Cor.originalComponentLambdaDifference_eq_principal
    (t := t) (qX := boundaryLineProjection R) (π := π) (F := f) (jB := j)
    (jA := chart R 0) (p := p) (α := α) (hA := chart_toSpec R 0)
    (hret := hret) (hbase := hq) (a := a) (vB := vB) (vA := vA)
    (hsmall := hsmall) (αorig := αorig) (βorig := βorig) (horig := horig)
    (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
    (H := H) (e := e) (ha := ha) (dB := d) (hdB := hd) (dA := dA)
    (hdA := hdA) (hcoverB := hcover) (hcoverA := hcoverA) (source := c)
    (LA := LA) (aA := aA) (bA := bA) (hpairA := hpairA)
    (hnormal := hnormal) (hfree := hfreeLocal) (W := W) (hW := hWcover)
    (r := r) (hr := hr) hgDirect
  exact hcor

end Motivic.PresheafWithTransfers
