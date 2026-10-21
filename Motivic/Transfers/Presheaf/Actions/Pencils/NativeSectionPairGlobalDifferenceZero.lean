/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairCanonicalPrincipalAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairDifferenceZero
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalLambdaDifference
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeOriginalComponentActions
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalTargetLambda
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterTargetMap

/-! # Global E3 action by descent of the original difference

Local shared-difference zero actions are produced internally on the actual
native component cover. Separatedness of the Nisnevich image descends the
action of the one global difference; the original global lambda equality is
then exposed at free geometry. No expanded local lambda-action theorem is
asserted here, and no such unaccepted wrapper is imported.
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

attribute [local instance]
  nativeSectionPairDifferenceZeroSmoothRelativeDimension

include hret hcover hbI hbE hFa hFb hpairA hsmall hcoverA in
/-- Descend the zero action of the unchanged global original difference.
The actual component cover may be empty; no whole-source integrality is used. -/
theorem nisnevichImage_transfer_nativeSectionPair_originalDifference_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hfree : ∀ k : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R k), ⊤) :=
        (scalarMap (pullback.snd f (chart R k))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R k), ⊤)) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π (chart R 0) dA z) aA) :=
      inferInstanceAs (IsIso (pullbackSectionMap
        (coprod.desc (infinityProductMap π (chart R 0) dA)
          (graphBoundaryRestriction π (chart R 0) z)) aA))
    (nisnevichImage P).transfer (Cor.originalLambdaDifference
      (t := t) (qX := boundaryLineProjection R) (π := π) (F := f) (jB := j)
      (jA := chart R 0) (p := p) (hret := hret) (hbase := hq)
      (a := a) (vB := vB) (vA := vA) (hsmall := hsmall)
      (αorig := αorig) (βorig := βorig) (horig := horig)
      (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
      (H := H) (e := e) (ha := ha) (dB := d) (hdB := hd) (dA := dA)
      (hcoverB := hcover) (hcoverA := hcoverA) (source := c)
      (LA := LA) (aA := aA) (bA := bA)) = 0 := by
  intro π haBoundary
  let Qsite := relativeTargetSite k t π (a ≫ chart R 0)
  let δ : Cor.mk (lambdaSourceSite k t (f ≫ π) j) ⟶ Cor.mk Qsite :=
    Cor.originalLambdaDifference
      (t := t) (qX := boundaryLineProjection R) (π := π) (F := f) (jB := j)
      (jA := chart R 0) (p := p) (hret := hret) (hbase := hq)
      (a := a) (vB := vB) (vA := vA) (hsmall := hsmall)
      (αorig := αorig) (βorig := βorig) (horig := horig)
      (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
      (H := H) (e := e) (ha := ha) (dB := d) (hdB := hd) (dA := dA)
      (hcoverB := hcover) (hcoverA := hcoverA) (source := c)
      (LA := LA) (aA := aA) (bA := bA)
  have hdesc := nisnevichImage_transfer_eq_of_nativeOriginalComponents
    R₀ p₀ O₀ V₀ k t (f ≫ π) j P Qsite δ 0 (by
      intro i
      let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
      have hi := transfer_nativeSectionPair_originalDifference_zero
        (R₀ := R₀) (p₀ := p₀) (O₀ := O₀) (V₀ := V₀) (R := R)
        (f := f) (j := j) (p := p) (hq := hq) (hret := hret)
        (a := a) (z := z) (s := s) (hs := hs) (H := H) (hsK := hsK)
        (e := e) (ha := ha) (d := d) (hd := hd) (c := c)
        (vB := vB) (vA := vA) (hsmall := hsmall) (hcover := hcover)
        (dA := dA) (hdA := hdA) (bI := bI) (hbI := hbI) (bE := bE) (hbE := hbE)
        (LA := LA) (aA := aA) (bA := bA) (iA := iA) (hFa := hFa) (hFb := hFb)
        (hpairA := hpairA) (αorig := αorig) (βorig := βorig) (horig := horig)
        (φorig := φorig) (hφorig := hφorig) (hcoverA := hcoverA)
        (Pst := nisnevichImage P) (hPst := nisnevichImage_isA1Invariant P hP) (t := t)
        i hfree
      have hfactor := Cor.originalComponentLambdaDifference_eq_comp_originalLambdaDifference
        (t := t) (qX := boundaryLineProjection R) (π := π) (F := f) (jB := j)
        (jA := chart R 0) (p := p) (hret := hret) (hbase := hq)
        (a := a) (vB := vB) (vA := vA) (hsmall := hsmall)
        (αorig := αorig) (βorig := βorig) (horig := horig)
        (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
        (H := H) (e := e) (ha := ha) (dB := d) (hdB := hd) (dA := dA)
        (hcoverB := hcover) (hcoverA := hcoverA) (source := c)
        (LA := LA) (aA := aA) (bA := bA)
        (α := α)
      have hlocal := (congrArg
        (fun z : Cor.mk (relativeCommonSite k t (f ≫ π) j α) ⟶ Cor.mk Qsite =>
          (nisnevichImage P).transfer z) hfactor).symm.trans hi
      exact hlocal.trans (by simp only [CategoryTheory.Limits.comp_zero, transfer_zero]))
  exact hdesc.trans (transfer_zero (nisnevichImage P) _ _)

end Motivic.PresheafWithTransfers
