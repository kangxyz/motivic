/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairCanonicalPrincipalAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairCorSpecialization
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalTargetLambda
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterTargetMap

/-! # Actual native zero action of the shared original difference

The same original native data internally produce one normalized unit and its
canonical principal zero action. The accepted native Cor supplier identifies
the shared original difference with that same principal correspondence.
No expanded lambda-action conversion is performed in this leaf.
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

namespace Motivic.PresheafWithTransfers
open Motivic.Cor

attribute [local instance] Cor.nativeOriginalPairTransferActionSmooth

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
  (hsK : (s ≫ j) ≫ f = z ≫ (chart R 0))
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


variable {B : Scheme.{u}} [IsAffine B]
  (αorig : B ⟶ finalOriginalSource R₀ p₀ O₀ V₀) [Smooth αorig]
  (βorig : B ⟶ A) [Flat βorig] (horig : αorig ≫ p = βorig ≫ a)
  (φorig : B ⟶ V) (hφorig : φorig ≫ (vB ≫ j) = αorig ≫ j)
  (hcoverA : ∀ x : ProjectiveSpace R (ULift.{u} (Fin 2)),
    x ∈ Set.range (a ≫ chart R 0) ∨ x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ chart R 0))
  {k : Type u} [Field k] (Pst : PresheafWithTransfers.{w} k) (hPst : Pst.IsA1Invariant)
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]

/-- The relative-dimension instance used in this module. -/
local instance nativeSectionPairDifferenceZeroSmoothRelativeDimension
    : SmoothOfRelativeDimension 1 ((a ≫ chart R 0) ≫
    ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

include hret hcover hbI hbE hFa hFb hpairA hPst hsmall hcoverA in
/-- The actual shared original difference has zero action, using the same
internally constructed normalized unit and no desired action premise. -/
theorem transfer_nativeSectionPair_originalDifference_zero
    (i : (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).I₀)
    (hfree : ∀ k : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R k), ⊤) :=
        (scalarMap (pullback.snd f (chart R k))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R k), ⊤)) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π (chart R 0) dA z) aA) :=
      inferInstanceAs (IsIso (pullbackSectionMap
        (coprod.desc (infinityProductMap π (chart R 0) dA)
          (graphBoundaryRestriction π (chart R 0) z)) aA))
    Pst.transfer (Cor.originalComponentLambdaDifference
      (t := t) (qX := boundaryLineProjection R) (π := π) (F := f) (jB := j)
      (jA := chart R 0) (p := p) (α := α) (hret := hret) (hbase := hq)
      (a := a) (vB := vB) (vA := vA) (hsmall := hsmall)
      (αorig := αorig) (βorig := βorig) (horig := horig)
      (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
      (H := H) (e := e) (ha := ha) (dB := d) (hdB := hd) (dA := dA)
      (hcoverB := hcover) (hcoverA := hcoverA) (source := c)
      (LA := LA) (aA := aA) (bA := bA)) = 0 := by
  intro π α haBoundary
  have hinfty : (Set.range (chart R 0))ᶜ ⊆ Set.range dA := by
    intro x hx
    rcases hcoverA x with ⟨y, hy⟩ | hy | ⟨y, hy⟩
    · exact False.elim (hx ⟨a y, hy⟩)
    · exact hy
    · exact False.elim (hx ⟨z y, hy⟩)
  have hpuncture : (Set.range a)ᶜ ⊆ Set.range z := by
    intro x hx
    rcases hcoverA (chart R 0 x) with ⟨y, hy⟩ | hy | ⟨y, hy⟩
    · exact False.elim (hx ⟨y, (chart R 0).isOpenEmbedding.injective hy⟩)
    · exact False.elim (Set.disjoint_left.mp hdA ⟨x, rfl⟩ hy)
    · exact ⟨y, (chart R 0).isOpenEmbedding.injective hy⟩
  obtain ⟨hT, hTN, haB, hcB, haA, hcA, hW, r, eW, heW, hr, hCov,
      hbase, hg, he, hzero⟩ :=
    exists_nativeSectionPairPrincipalAction_zero_canonical R₀ p₀ O₀ V₀ R f j p hq hret
      a z s hs H hsK e ha d hd c (vB ≫ j) hcover dA hdA bI hbI bE hbE
      LA aA bA iA hFa hFb hpairA Pst hPst t hinfty hpuncture i hfree
  let := hT
  let := hTN
  let := haB
  let := hcB
  let := haA
  let := hcA
  let := hW
  -- The accepted native Cor supplier prepares geometry and norm coherence once.
  have hcor := nativeSectionPair_originalLambda_eq_principal
    (R₀ := R₀) (p₀ := p₀) (O₀ := O₀) (V₀ := V₀) (R := R)
    (f := f) (j := j) (p := p) (hq := hq) (hret := hret)
    (a := a) (z := z) (s := s) (hs := hs) (H := H) (e := e) (ha := ha)
    (d := d) (hd := hd) (c := c) (vB := vB) (vA := vA) (hsmall := hsmall)
    (hcover := hcover) (dA := dA) (hdA := hdA) (LA := LA) (aA := aA) (bA := bA)
    (iA := iA) (hFa := hFa) (hFb := hFb) (hpairA := hpairA)
    (αorig := αorig) (βorig := βorig) (horig := horig)
    (φorig := φorig) (hφorig := hφorig) (hcoverA := hcoverA) (k := k) (t := t)
    i hfree hT hTN haB hcB haA hcA hW r hr eW hCov hg
  have hDifferenceZero := (congrArg
    (fun z : Cor.mk (relativeCommonSite k t (f ≫ π) j α) ⟶
      Cor.mk (relativeTargetSite k t π (a ≫ chart R 0)) => Pst.transfer z) hcor).trans hzero
  exact hDifferenceZero

end Motivic.PresheafWithTransfers
