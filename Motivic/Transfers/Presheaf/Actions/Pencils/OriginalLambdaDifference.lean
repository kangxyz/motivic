/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalComponentLambdaDifference

/-! # The global original lambda difference and its component restrictions

One global original difference retains the original source record and target
pair. Its component restriction is the accepted shared component difference.
Only correspondence functoriality and additivity enter these free-geometry
bridges; there is no integral or nonempty global-source hypothesis.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom Scheme.RelativeCurvePencil
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
universe u w
namespace Motivic.Cor
open Scheme Scheme.RelativeCurvePencil Scheme.Hom
attribute [local instance] Motivic.Cor.instSmoothOfSmoothOfRelativeDimensionOfNatNat

variable {k : Type u} [Field k]
  {S C P X Y K A V B Z DB DA : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine K] [IsIntegral K]
  [IsAffine A] [IsAffine V] [IsAffine B]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (qX : X ⟶ S) [IsSeparated qX] [SmoothOfRelativeDimension 1 qX]
  (π : P ⟶ S) [IsProper π] (F : C ⟶ P) [IsFinite F]
  (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ (F ≫ π))]
  (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (α : K ⟶ Y) [Smooth α] [Flat α]
  (hA : jA ≫ π = qX) (hret : jB ≫ F = p ≫ jA)
  (hbase : jB ≫ (F ≫ π) = p ≫ qX)
  (a : A ⟶ X) [IsOpenImmersion a]
  (vB : V ⟶ Y) [IsOpenImmersion vB] (vA : V ⟶ A)
  (hsmall : vB ≫ p = vA ≫ a)
  [SmoothOfRelativeDimension 1 ((vB ≫ jB) ≫ (F ≫ π))]
  [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
  (αorig : B ⟶ Y) [Smooth αorig] (βorig : B ⟶ A) [Flat βorig]
  (horig : αorig ≫ p = βorig ≫ a)
  (φorig : B ⟶ V) (hφorig : φorig ≫ (vB ≫ jB) = αorig ≫ jB)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback qX (z ≫ qX)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget qX z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (dB : DB ⟶ C) (hdB : Disjoint (Set.range jB) (Set.range dB))
  (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (hcoverB : ∀ x : C, x ∈ Set.range (vB ≫ jB) ∨
    x ∈ Set.range dB ∨ x ∈ Set.range (s ≫ jB))
  (hcoverA : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨
    x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ jA))
  (source : BoundarySectionData qX (F ≫ π) jB p hbase a z s hs H e ha dB hdB)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA)]
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bA)]
  (hpairA :
    pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA ≫
        pullbackTensorMap (fullBoundaryProductMap π jA dA z) LA.val
          (dualLineBundle _ (relativeCompactificationGraphLine π jA)).val =
      tensorUnitSection (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bA)
        (relativeFullBoundaryFrame qX π jA (𝟙 _)
          (hA.trans (Category.id_comp qX).symm) z z (Category.comp_id z)
          (IsPullback.id_vert z) e dA hdA).inv)

local notation "siteK" => (relativeCommonSite k t (F ≫ π) jB α)
local notation "siteY" => (lambdaSourceSite k t (F ≫ π) jB)
local notation "siteX" => (lambdaSourceSite k t π jA)
local notation "siteQ" => (relativeTargetSite k t π (a ≫ jA))
local notation "siteV" => (relativeTargetSite k t (F ≫ π) (vB ≫ jB))
local instance : IsAffine (siteK).left := by
  change IsAffine K
  infer_instance
local instance : IsAffine (siteY).left := by
  change IsAffine Y
  infer_instance
local instance : IsAffine (siteX).left := by
  change IsAffine X
  infer_instance
local instance : IsAffine (siteQ).left := by
  change IsAffine A
  infer_instance

/-- The two unchanged original global lambda correspondences, as one difference. -/
def originalLambdaDifference : Cor.mk siteY ⟶ Cor.mk siteQ :=
    let pSite : siteY ⟶ siteX := SmoothSite.homMk p (by
      change p ≫ ((jA ≫ π) ≫ t) = (jB ≫ (F ≫ π)) ≫ t
      simpa only [Category.assoc] using
        congrArg (fun m => m ≫ π ≫ t) hret.symm)
    let vASite : siteV ⟶ siteQ := SmoothSite.homMk vA (by
      change vA ≫ (((a ≫ jA) ≫ π) ≫ t) = ((vB ≫ jB) ≫ (F ≫ π)) ≫ t
      rw [Category.assoc, Category.assoc, ← Category.assoc vA a, ← hsmall]
      simpa only [Category.assoc] using
        congrArg (fun m => vB ≫ m ≫ π ≫ t) hret.symm)
    let data := source.toData k t qX (F ≫ π) jB p hbase a αorig βorig horig
      z s hs H e ha dB hdB (vB ≫ jB) hcoverB φorig hφorig
    (data.lam ≫ (graphFunctor k).map vASite : Cor.mk siteY ⟶ Cor.mk siteQ) -
    ((graphFunctor k).map pSite ≫
        originalTargetLambda k t π jA z dA a hcoverA LA aA bA :
          Cor.mk siteY ⟶ Cor.mk siteQ)

omit [IsIntegral K] [Flat α] in
/-- Restricting the one global difference gives the unchanged component difference. -/
theorem originalComponentLambdaDifference_eq_comp_originalLambdaDifference :
    originalComponentLambdaDifference
      (t := t) (qX := qX) (π := π) (F := F) (jB := jB) (jA := jA)
      (p := p) (α := α) (hret := hret) (hbase := hbase) (a := a)
      (vB := vB) (vA := vA) (hsmall := hsmall)
      (αorig := αorig) (βorig := βorig) (horig := horig)
      (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
      (H := H) (e := e) (ha := ha) (dB := dB) (hdB := hdB) (dA := dA)
      (hcoverB := hcoverB) (hcoverA := hcoverA) (source := source)
      (LA := LA) (aA := aA) (bA := bA) =
    (graphFunctor k).map (relativeAlpha k t (F ≫ π) jB α) ≫
      originalLambdaDifference
      (t := t) (qX := qX) (π := π) (F := F) (jB := jB) (jA := jA)
      (p := p) (hret := hret) (hbase := hbase) (a := a)
      (vB := vB) (vA := vA) (hsmall := hsmall)
      (αorig := αorig) (βorig := βorig) (horig := horig)
      (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
      (H := H) (e := e) (ha := ha) (dB := dB) (hdB := hdB) (dA := dA)
      (hcoverB := hcoverB) (hcoverA := hcoverA) (source := source)
      (LA := LA) (aA := aA) (bA := bA) := by
  simp only [originalComponentLambdaDifference, originalLambdaDifference,
    Preadditive.comp_sub, Functor.map_comp, Category.assoc]

/-- Zero action of the global difference is the original global action equality. -/
theorem originalLambda_action_eq_of_difference_zero
    (Pst : Motivic.PresheafWithTransfers.{w} k)
    (hz : Pst.transfer (originalLambdaDifference
      (t := t) (qX := qX) (π := π) (F := F) (jB := jB) (jA := jA)
      (p := p) (hret := hret) (hbase := hbase) (a := a)
      (vB := vB) (vA := vA) (hsmall := hsmall)
      (αorig := αorig) (βorig := βorig) (horig := horig)
      (φorig := φorig) (hφorig := hφorig) (z := z) (s := s) (hs := hs)
      (H := H) (e := e) (ha := ha) (dB := dB) (hdB := hdB) (dA := dA)
      (hcoverB := hcoverB) (hcoverA := hcoverA) (source := source)
      (LA := LA) (aA := aA) (bA := bA)) = 0) :
    let pSite : siteY ⟶ siteX := SmoothSite.homMk p (by
      change p ≫ ((jA ≫ π) ≫ t) = (jB ≫ (F ≫ π)) ≫ t
      simpa only [Category.assoc] using
        congrArg (fun m => m ≫ π ≫ t) hret.symm)
    let vASite : siteV ⟶ siteQ := SmoothSite.homMk vA (by
      change vA ≫ (((a ≫ jA) ≫ π) ≫ t) = ((vB ≫ jB) ≫ (F ≫ π)) ≫ t
      rw [Category.assoc, Category.assoc, ← Category.assoc vA a, ← hsmall]
      simpa only [Category.assoc] using
        congrArg (fun m => vB ≫ m ≫ π ≫ t) hret.symm)
    let data := source.toData k t qX (F ≫ π) jB p hbase a αorig βorig horig
      z s hs H e ha dB hdB (vB ≫ jB) hcoverB φorig hφorig
    Pst.transfer (data.lam ≫ (graphFunctor k).map vASite : Cor.mk siteY ⟶ Cor.mk siteQ) =
    Pst.transfer ((graphFunctor k).map pSite ≫
        originalTargetLambda k t π jA z dA a hcoverA LA aA bA :
          Cor.mk siteY ⟶ Cor.mk siteQ) := by
  intro pSite vASite data
  have hz' : Pst.transfer ((data.lam ≫ (graphFunctor k).map vASite : Cor.mk siteY ⟶ Cor.mk siteQ) -
    ((graphFunctor k).map pSite ≫
        originalTargetLambda k t π jA z dA a hcoverA LA aA bA :
          Cor.mk siteY ⟶ Cor.mk siteQ)) = 0 := hz
  rw [Motivic.PresheafWithTransfers.transfer_sub] at hz'
  exact sub_eq_zero.mp hz'

end Motivic.Cor
