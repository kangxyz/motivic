/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.OriginalPresentationAffineCombinedCorrection
public import Motivic.Cohomology.A1.PresheafBoundaryAffineWeilDescent
public import Motivic.Cohomology.A1.RestrictionDifferenceRestriction
public import Motivic.Cohomology.A1.PresheafBoundaryOriginalOpenRefinement
public import Motivic.Cohomology.A1.PresheafBoundaryPolynomialOverlap
public import Motivic.AlgebraicGeometry.LargePrimeNativePolynomialPresentation
public import Motivic.AlgebraicGeometry.SmoothSiteFiniteScalarOpenFactor
public import Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialOverlap
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineCorrectionRestriction

/-! # Finite polynomial corrections on the original boundary

Two actual coprime scalar presentations produce affine corrections over one
original affine base open. Their restricted witnesses retain the original
ambient, full zero sections and signed equations on the actual punctures.
The constructed affine Weil refinement then gives the canonical image witness
on the original open arrow, for the unchanged presheaf with transfers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic.PresheafWithTransfers Motivic.SmoothSiteAffineCoordinates
open AlgebraicGeometry.Scheme.RelativeCurve
open scoped TensorProduct

universe u

namespace Motivic.FiniteEtaleSite.OriginalPresheaf

variable {k : Type u} [Field k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance {R L : Type u} [CommRing R] [Field L] [Algebra k R] [Algebra k L]
    [Algebra.Smooth k R] : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

private structure ScalarAffineWitness
    (P : PresheafWithTransfers.{u + 1} k) (L : Type u) [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    {V Y D : SmoothSite (Spec (.of k))}
    (q : Y ⟶ SmoothSite.a1Cylinder (.of k) V) [Etale q.left] (z : V ⟶ Y)
    (φ : SmoothSite.etalePullback q (SmoothSite.contractionOpen (.of k) V) ⟶ D)
    (s : sections P (Cor.mk D)) where
  E : SmoothSite (Spec (.of L))
  affine : IsAffine E.left
  f : E ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj Y
  etale : Etale f.left
  mark : (SmoothSite.fieldBaseChange (algebraMap k L)).obj V ⟶ E
  mark_eq : mark ≫ f = (SmoothSite.fieldBaseChange (algebraMap k L)).map z
  laurentSection : sections (finiteSeparableExtension L P)
    (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L)).obj
      (SmoothSite.torusCylinder (.of k) V)))
  ambientSection : sections (finiteSeparableExtension L P) (Cor.mk E)
  relation :
    letI := etale
    let F := SmoothSite.fieldBaseChange (algebraMap k L)
    let α := SmoothSite.etalePullbackFst q (SmoothSite.contractionOpen (.of k) V)
    let β := SmoothSite.etalePullbackSnd q (SmoothSite.contractionOpen (.of k) V)
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.etalePullbackSnd f (F.map α) ≫ F.map β)) laurentSection -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.etalePullbackFst f (F.map α))) ambientSection =
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.etalePullbackSnd f (F.map α) ≫ F.map φ))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)

/-- Native scalar affine-line comparisons retain every original base map. -/
theorem _root_.Motivic.SmoothSite.fieldBaseChangeA1Iso_naturality
    {L : Type u} [Field L] [Algebra k L]
    {U V : SmoothSite (Spec (.of k))} (j : U ⟶ V) :
    (SmoothSite.fieldBaseChange (algebraMap k L)).map (SmoothSite.a1Map (.of k) j) ≫
      (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom =
    (SmoothSite.fieldBaseChangeA1Iso (L := L) U).hom ≫
      SmoothSite.a1Map (.of L) ((SmoothSite.fieldBaseChange (algebraMap k L)).map j) := by
  apply SmoothSite.product_hom_ext
  · simp [SmoothSite.fieldBaseChangeA1Iso, SmoothSite.a1Map,
      SmoothSite.fieldBaseChange, SmoothSite.finiteSeparableBaseMap, ← Functor.map_comp]
  · simp only [SmoothSite.a1Map, Category.assoc, SmoothSite.productMap_snd,
      Category.comp_id, SmoothSite.fieldBaseChangeA1Iso_snd, SmoothSite.fieldBaseChange,
      SmoothSite.finiteSeparableBaseMap]
    rw [← Functor.map_comp_assoc, SmoothSite.productMap_snd, Category.comp_id]

private theorem restrictScalarAffineWitness
    (P : PresheafWithTransfers.{u + 1} k)
    {L : Type u} [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    {V U Y YU D A : SmoothSite (Spec (.of k))}
    [IsAffine Y.left] [IsAffine YU.left]
    (j : U ⟶ V) (q₀ : Y ⟶ SmoothSite.a1Cylinder (.of k) V)
    (qU : YU ⟶ SmoothSite.a1Cylinder (.of k) U) [Etale qU.left]
    (r : YU ⟶ Y) (hr : r ≫ q₀ = qU ≫ SmoothSite.a1Map (.of k) j)
    (z₀ : V ⟶ Y) (zU : U ⟶ YU) (hzr : zU ≫ r = j ≫ z₀)
    (e₀ : Y ⟶ A) (δ : D ⟶ A)
    [Mono ((SmoothSite.fieldBaseChange (algebraMap k L)).map δ)]
    (φU : SmoothSite.etalePullback qU (SmoothSite.contractionOpen (.of k) U) ⟶ D)
    (hφU : φU ≫ δ = SmoothSite.etalePullbackFst qU
      (SmoothSite.contractionOpen (.of k) U) ≫ r ≫ e₀)
    {B E O : SmoothSite (Spec (.of L))} [IsAffine E.left]
    (i : B ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj V)
    [Mono (SmoothSite.a1Map (.of L) i)]
    (bU : (SmoothSite.fieldBaseChange (algebraMap k L)).obj U ⟶ B)
    (hbU : bU ≫ i = (SmoothSite.fieldBaseChange (algebraMap k L)).map j)
    (η : E ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj Y) [Etale η.left]
    (q : E ⟶ SmoothSite.a1Cylinder (.of L) B)
    (hq : η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map q₀ ≫
      (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom = q ≫ SmoothSite.a1Map (.of L) i)
    (ζ : B ⟶ E)
    (hζη : ζ ≫ η = i ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map z₀)
    (α : O ⟶ E) (β : O ⟶ SmoothSite.torusCylinder (.of L) B)
    (H : IsPullback β.left α.left (SmoothSite.contractionOpen (.of L) B).left q.left)
    (φ : O ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj D)
    (hφ : φ ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map δ =
      α ≫ η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map e₀)
    (s : sections P (Cor.mk D))
    (a : sections (finiteSeparableExtension L P) (Cor.mk (SmoothSite.torusCylinder (.of L) B)))
    (c : sections (finiteSeparableExtension L P) (Cor.mk E))
    (h : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map β) a -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map α) c =
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map φ)
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)) :
    Nonempty (ScalarAffineWitness P L qU zU φU s) := by
  let F := SmoothSite.fieldBaseChange (algebraMap k L)
  let : IsAffineHom Y.hom := isAffineHom_of_isAffine
    (show Y.left ⟶ Spec (.of k) from Y.hom)
  let : IsAffineHom YU.hom := isAffineHom_of_isAffine
    (show YU.left ⟶ Spec (.of k) from YU.hom)
  let : IsAffine (F.obj Y).left := inferInstanceAs
    (IsAffine (pullback Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
  let : IsAffine (F.obj YU).left := inferInstanceAs
    (IsAffine (pullback YU.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
  let E' := SmoothSite.etalePullback η (F.map r)
  let l := SmoothSite.etalePullbackFst η (F.map r)
  let f := SmoothSite.etalePullbackSnd η (F.map r)
  have hE' : IsAffine E'.left := inferInstanceAs
    (IsAffine (pullback η.left (F.map r).left))
  have hf : Etale f.left := inferInstanceAs (Etale (pullback.snd η.left (F.map r).left))
  let := hf
  have hlf : l ≫ η = f ≫ F.map r := (SmoothSite.etalePullbackCone η (F.map r)).condition
  have hm : (bU ≫ ζ) ≫ η = F.map zU ≫ F.map r := by
    rw [Category.assoc, hζη, ← Category.assoc, hbU, ← Functor.map_comp,
      ← hzr, Functor.map_comp]
  have HP : IsPullback l f η (F.map r) :=
    IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit η (F.map r))
  let mark := HP.lift (bU ≫ ζ) (F.map zU) hm
  let cU := (SmoothSite.fieldBaseChangeA1Iso (L := L) U).hom ≫ SmoothSite.a1Map (.of L) bU
  let tU := (SmoothSite.fieldBaseChangeTorusCylinderIso (L := L) U).hom ≫
    SmoothSite.productMap bU (𝟙 (SmoothSite.torus (.of L)))
  have hlq : l ≫ q = f ≫ F.map qU ≫ cU := by
    apply (cancel_mono (SmoothSite.a1Map (.of L) i)).mp
    calc
      _ = l ≫ η ≫ F.map q₀ ≫ (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom := by
        rw [Category.assoc, ← hq]
      _ = f ≫ F.map (qU ≫ SmoothSite.a1Map (.of k) j) ≫
          (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom := by
        rw [← Category.assoc l, hlf, Category.assoc, ← Functor.map_comp_assoc, hr]
      _ = f ≫ F.map qU ≫ (SmoothSite.fieldBaseChangeA1Iso (L := L) U).hom ≫
          SmoothSite.a1Map (.of L) (bU ≫ i) := by
        rw [Functor.map_comp, Category.assoc, SmoothSite.fieldBaseChangeA1Iso_naturality, ← hbU]
      _ = (f ≫ F.map qU ≫ cU) ≫ SmoothSite.a1Map (.of L) i := by
        simp only [cU, SmoothSite.a1Map_comp, Category.assoc]
  have htj : tU ≫ SmoothSite.contractionOpen (.of L) B =
      F.map (SmoothSite.contractionOpen (.of k) U) ≫ cU := by
    dsimp only [tU, cU]
    rw [Category.assoc, ← SmoothSite.contractionOpen_naturality,
      ← Category.assoc, ← SmoothSite.fieldBaseChangeA1Iso_contractionOpen]
    simp only [Category.assoc]
    rfl
  let αU := SmoothSite.etalePullbackFst qU (SmoothSite.contractionOpen (.of k) U)
  let βU := SmoothSite.etalePullbackSnd qU (SmoothSite.contractionOpen (.of k) U)
  have hU : βU ≫ SmoothSite.contractionOpen (.of k) U = αU ≫ qU :=
    (SmoothSite.etalePullbackCone qU (SmoothSite.contractionOpen (.of k) U)).condition.symm
  have hlη : l ≫ (η ≫ F.map e₀) = f ≫ F.map (r ≫ e₀) := by
    rw [← Category.assoc, hlf, Category.assoc, Functor.map_comp]
  refine ⟨{
    E := E'
    affine := hE'
    f := f
    etale := hf
    mark := mark
    mark_eq := HP.lift_snd _ _ _
    laurentSection := transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map tU) a
    ambientSection := transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map l) c
    relation := ?_ }⟩
  exact restriction_difference_on_scalar_etale_pullback P αU βU qU
    (SmoothSite.contractionOpen (.of k) U) hU φU δ (r ≫ e₀) hφU
    f l q (SmoothSite.contractionOpen (.of L) B) tU cU hlq htj α β H
    (η ≫ F.map e₀) hlη φ hφ _ a c h

private structure ProducedScalarCorrection
    (P : PresheafWithTransfers.{u + 1} k) (L : Type u) [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    {V Y D A : SmoothSite (Spec (.of k))} (w : V.left)
    (q₀ : Y ⟶ SmoothSite.a1Cylinder (.of k) V) (z₀ : V ⟶ Y)
    (δ : D ⟶ A) (e₀ : Y ⟶ A) (s : sections P (Cor.mk D)) where
  B : SmoothSite (Spec (.of L))
  i : B ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj V
  open_i : IsOpenImmersion i.left
  fiber : (SmoothSite.finiteScalarProjection (E := L) V).left ⁻¹' {w} ⊆ Set.range i.left
  E : SmoothSite (Spec (.of L))
  affine_E : IsAffine E.left
  η : E ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj Y
  etale_η : Etale η.left
  q : E ⟶ SmoothSite.a1Cylinder (.of L) B
  base_eq : η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map q₀ ≫
    (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom = q ≫ SmoothSite.a1Map (.of L) i
  ζ : B ⟶ E
  mark_eq : ζ ≫ η = i ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map z₀
  O : SmoothSite (Spec (.of L))
  α : O ⟶ E
  β : O ⟶ SmoothSite.torusCylinder (.of L) B
  square : IsPullback β.left α.left (SmoothSite.contractionOpen (.of L) B).left q.left
  φ : O ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj D
  ambient_eq : φ ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map δ =
    α ≫ η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map e₀
  a : sections (finiteSeparableExtension L P) (Cor.mk (SmoothSite.torusCylinder (.of L) B))
  c : sections (finiteSeparableExtension L P) (Cor.mk E)
  relation : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map β) a -
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map α) c =
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map φ)
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)

private theorem produceScalarCorrection
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (R L : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [Field L] [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]
    {Y D A : SmoothSite (Spec (.of k))}
    (p : Y ⟶ RelativePolynomialOpenSpans.lineSite (k := k) (R := R)) [Etale p.left]
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (w : Spec (.of R)) (wL : Spec (.of (R ⊗[k] L)))
    (hu : ∀ v : Spec (.of (R ⊗[k] L)),
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) v = w → v = wL)
    (δ : D ⟶ A) (e₀ : Y ⟶ A)
    (τ : SmoothSite.etalePullback p
      (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)) ⟶ D)
    (hτ : τ ≫ δ = SmoothSite.etalePullbackFst p
      (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫ e₀)
    (s : sections P (Cor.mk D))
    (hFY : IsAffine ((SmoothSite.fieldBaseChange (algebraMap k L)).obj Y).left)
    (hpL : Etale ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫
      (scalarLineIso k R L).hom).left)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial (R ⊗[k] L))))
    (σ : Z ⟶ ((SmoothSite.fieldBaseChange (algebraMap k L)).obj Y).left)
    (presentation : AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation L
      (RelativePolynomialOpenSpans.lineSite (k := L) (R := R ⊗[k] L)).hom
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫ (scalarLineIso k R L).hom).left
      (RelativePolynomialOpenSpans.openInclusion (k := L)
        (Polynomial.X : Polynomial (R ⊗[k] L))).left z σ
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L))) wL))
    (hsL : ((SmoothSite.affineScalarIso k R L).inv ≫
      (SmoothSite.fieldBaseChange (algebraMap k L)).map
        (polynomialZeroLiftSite k R p s₀ hs₀)).left ≫
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫ (scalarLineIso k R L).hom).left =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L)))) :
    Nonempty (ProducedScalarCorrection P L w (p ≫ lineCylinderIso.hom)
      (polynomialZeroLiftSite k R p s₀ hs₀) δ e₀ s) := by
  let F := SmoothSite.fieldBaseChange (algebraMap k L)
  let pL := F.map p ≫ (scalarLineIso k R L).hom
  let V := AffineTorusPolynomialPresentation.affineSite k R
  let z₀ := polynomialZeroLiftSite k R p s₀ hs₀
  let : Algebra.Smooth L (R ⊗[k] L) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)
  let : IsAffine (F.obj Y).left := hFY
  let : Etale pL.left := hpL
  obtain ⟨B, v, _hB, hv, hwB, E, η, q, ζ, hE, hη, hq, hbase, hζq, hζη,
      O, α, β, φ, H, hφ, hL⟩ :=
    OriginalEtalePresentation.exists_original_affine_torus_neighborhood_lifting
      (R ⊗[k] L) pL z σ wL presentation
        (finiteSeparableExtension L P) (finiteSeparableExtension_isA1Invariant L P hP)
        ((SmoothSite.affineScalarIso k R L).inv ≫ F.map z₀).left hsL
  let : IsOpenImmersion v.left := hv
  let : IsIso (SmoothSite.affineScalarIso k R L).inv.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of L))).mapIso
      (SmoothSite.affineScalarIso k R L)).inv)
  let i := v ≫ (SmoothSite.affineScalarIso k R L).inv
  have hi : IsOpenImmersion i.left := inferInstanceAs
    (IsOpenImmersion (v.left ≫ (SmoothSite.affineScalarIso k R L).inv.left))
  have hfiber : (SmoothSite.finiteScalarProjection (E := L) V).left ⁻¹' {w} ⊆
      Set.range i.left := by
    intro y hy
    obtain ⟨b, hb⟩ := hwB
    have hy' : Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L)))
        ((SmoothSite.affineScalarIso k R L).hom.left y) = w := by
      have he := congrArg (fun f => f y) (SmoothSite.affineScalarIso_hom_original k R L)
      exact he.trans hy
    have he := hu _ hy'
    refine ⟨b, ?_⟩
    change (SmoothSite.affineScalarIso k R L).inv.left (v.left b) = y
    rw [hb, ← he]
    exact congrArg (fun f => f y)
      (((SmoothSite.forgetScheme (Spec (.of L))).mapIso
        (SmoothSite.affineScalarIso k R L)).hom_inv_id)
  let ζs : B ⟶ E := SmoothSite.homMk ζ (by
    rw [← MorphismProperty.Over.w q, ← Category.assoc, hζq]
    exact MorphismProperty.Over.w (SmoothSite.a1Section (.of L) B 0))
  have hmark : ζs ≫ η = i ≫ F.map z₀ := by
    apply MorphismProperty.Over.Hom.ext
    exact hζη
  let : IsIso (SmoothSite.a1Map (.of L) (SmoothSite.affineScalarIso k R L).hom) :=
    inferInstanceAs (IsIso (cylinderIso (SmoothSite.affineScalarIso k R L)).hom)
  have hbase' : η ≫ F.map (p ≫ lineCylinderIso.hom) ≫
      (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom = q ≫ SmoothSite.a1Map (.of L) i := by
    apply (cancel_mono (SmoothSite.a1Map (.of L) (SmoothSite.affineScalarIso k R L).hom)).mp
    calc
      _ = η ≫ pL ≫ (lineCylinderIso (k := L) (R := R ⊗[k] L)).hom := by
        simp only [pL, scalarLineIso, Iso.trans_hom, Iso.symm_hom,
          Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.inv_hom_id,
          Category.comp_id, cylinderIso, SmoothSite.a1Map]
        rfl
      _ = q ≫ SmoothSite.a1Map (.of L) v := hbase
      _ = (q ≫ SmoothSite.a1Map (.of L) i) ≫
          SmoothSite.a1Map (.of L) (SmoothSite.affineScalarIso k R L).hom := by
        simp only [i, SmoothSite.a1Map_comp, Category.assoc]
        rw [← SmoothSite.a1Map_comp, Iso.inv_hom_id, SmoothSite.a1Map_id, Category.comp_id]
  let τL := scalarPolynomialOverlapMap k R L p ≫ F.map τ
  let ψ := φ ≫ τL
  have hψ : ψ ≫ F.map δ = α ≫ η ≫ F.map e₀ := by
    dsimp only [ψ, τL]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, hτ, Functor.map_comp,
      ← Category.assoc (scalarPolynomialOverlapMap k R L p), scalarPolynomialOverlapMap_fst,
      ← Category.assoc φ, hφ, Category.assoc]
  obtain ⟨a, c, hac⟩ := (HasRestrictionDifferenceLifting.restrict
    (finiteSeparableExtension L P) hL τL)
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)
  exact ⟨{
    B := B
    i := i
    open_i := hi
    fiber := hfiber
    E := E
    affine_E := hE
    η := η
    etale_η := hη
    q := q
    base_eq := hbase'
    ζ := ζs
    mark_eq := hmark
    O := O
    α := α
    β := β
    square := H
    φ := ψ
    ambient_eq := hψ
    a := a
    c := c
    relation := hac }⟩

/-- Actual coprime scalar presentations give an image witness on an original open
neighborhood. No scalar correction or common-refinement family is supplied. -/
theorem exists_finite_polynomial_boundary_image_neighborhood
    [Finite k] (X : SmoothSite (Spec (.of k)))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (W : FiniteEtaleSite (SmoothSite.a1Cylinder (.of k) X).left)
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ RelativePolynomialOpenSpans.lineSite (k := k) (R := R)) [Etale p.left]
    (w : Spec (.of R))
    [(PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) w).asIdeal.IsMaximal]
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (H₀ : IsPullback s₀ (𝟙 _) p.left
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))))
    (v₀ : AffineTorusPolynomialPresentation.affineSite k R ⟶
      (toSmoothSite X).obj ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W))
    [IsOpenImmersion v₀.left]
    (e₀ : Y ⟶ (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W)
    (hp : p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
      SmoothSite.a1Map (.of k)
        (v₀ ≫ toBase X ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W)) =
      e₀ ≫ toBase (SmoothSite.a1Cylinder (.of k) X) W)
    (hmark : s₀ ≫ e₀.left = v₀.left ≫
      pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left)
    (d : ((PresheafWithTransfers.toPresheaf k).obj P).obj (op
      ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
        ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W)))) :
    ∃ (V : FiniteEtaleSite X.left)
      (v : V ⟶ (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W),
      IsOpenImmersion v.left ∧ v₀.left w ∈ Set.range v.left ∧
      Presheaf.imageSieve (contractionToBoundary X P).hom
        ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
          (SmoothSite.contractionOpen (.of k) X)
          (SmoothSite.a1Section (.of k) X 0)).app (op W) d) v := by
  let V₀ := AffineTorusPolynomialPresentation.affineSite k R
  let q₀ := p ≫ (lineCylinderIso (k := k) (R := R)).hom
  let : IsIso (lineCylinderIso (k := k) (R := R)).hom.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme _).mapIso lineCylinderIso).hom)
  let : Etale q₀.left := inferInstanceAs
    (Etale (p.left ≫ (lineCylinderIso (k := k) (R := R)).hom.left))
  let z₀ := polynomialZeroLiftSite k R p s₀ hs₀
  have hz₀ : z₀ ≫ q₀ = SmoothSite.a1Section (.of k) V₀ 0 := by
    rw [show z₀ ≫ q₀ = (z₀ ≫ p) ≫ lineCylinderIso.hom from (Category.assoc ..).symm,
      polynomialZeroLiftSite_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let δ := (restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app W
  let τ := polynomialOverlapToPunctured X
    (v₀ ≫ toBase X ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W)) W p e₀ hp
  have hτ : τ ≫ δ = SmoothSite.etalePullbackFst p
      (RelativePolynomialOpenSpans.openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫ e₀ := by
    apply MorphismProperty.Over.Hom.ext
    exact polynomialOverlapToPunctured_fst X _ W p e₀ hp
  obtain ⟨n, m, hn, hm, hnm, hdata⟩ :=
    exists_two_prime_nativePolynomial_presentations k R ℓ w p s₀ hs₀ H₀ 0
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let L₁ := ULift.{u} (FiniteField.Extension k ℓ n)
  let L₂ := ULift.{u} (FiniteField.Extension k ℓ m)
  obtain ⟨hd₁, hY₁, hp₁, w₁, _, hu₁, ⟨e₁⟩, hz₁⟩ := hdata n (Or.inl rfl)
  obtain ⟨hd₂, hY₂, hp₂, w₂, _, hu₂, ⟨e₂⟩, hz₂⟩ := hdata m (Or.inr rfl)
  obtain ⟨c₁⟩ := produceScalarCorrection P hP R L₁ p s₀ hs₀ w w₁ hu₁
    δ e₀ τ hτ d hY₁ hp₁ _ _ e₁ hz₁
  obtain ⟨c₂⟩ := produceScalarCorrection P hP R L₂ p s₀ hs₀ w w₂ hu₂
    δ e₀ τ hτ d hY₂ hp₂ _ _ e₂ hz₂
  let := c₁.open_i
  let := c₂.open_i
  obtain ⟨U₀, hU₀, hwU, b₁, b₂, hb₁, hb₂⟩ :=
    SmoothSite.exists_common_affine_scalar_open_factor V₀ w c₁.i c₂.i c₁.fiber c₂.fiber
  let : IsAffine U₀.toScheme := hU₀
  let U₁ := SmoothSite.mk (U₀.ι ≫ V₀.hom)
  let j : U₁ ⟶ V₀ := SmoothSite.homMk U₀.ι rfl
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U₀.ι)
  let V := originalOpenBase X W v₀ j
  let eU := originalOpenBaseIso X W v₀ j
  let U := (toSmoothSite X).obj V
  let : IsAffine U.left := hU₀
  let j' : U ⟶ V₀ := eU.inv ≫ j
  let v := originalOpenBaseToZero X W v₀ j
  have hbase : j' ≫ v₀ ≫ toBase X
      ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W) = toBase X V := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 _ ≫ U₀.ι) ≫ v₀.left ≫ _ = _
    simp only [Category.id_comp]
    rfl
  let YU := SmoothSite.originalOpenRefinement q₀ j'
  let : IsAffine V₀.left := inferInstanceAs (IsAffine (Spec (.of R)))
  let : IsAffine YU.left := SmoothSite.originalOpenRefinement_affine q₀ j'
  let qU := SmoothSite.originalOpenRefinementCylinder q₀ j'
  let : Etale qU.left := SmoothSite.originalOpenRefinementCylinder_etale q₀ j'
  let r := SmoothSite.originalOpenRefinementAmbient q₀ j'
  let zU := SmoothSite.originalOpenRefinementZero q₀ j' z₀ hz₀
  let φU := originalOpenRefinementToPunctured X W v₀ j' q₀ e₀ hp
  have hφU : φU ≫ δ = SmoothSite.etalePullbackFst qU
      (SmoothSite.contractionOpen (.of k) U) ≫ r ≫ e₀ := by
    apply MorphismProperty.Over.Hom.ext
    exact originalOpenRefinementToPunctured_fst X W v₀ j' q₀ e₀ hp
  have restrict (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
      [Algebra.IsSeparable k L]
      (c : ProducedScalarCorrection P L w q₀ z₀ δ e₀ d)
      (b : (SmoothSite.fieldBaseChange (algebraMap k L)).obj U₁ ⟶ c.B)
      (hb : b ≫ c.i = (SmoothSite.fieldBaseChange (algebraMap k L)).map j) :
      Nonempty (ScalarAffineWitness P L qU zU φU d) := by
    let F := SmoothSite.fieldBaseChange (algebraMap k L)
    let := c.affine_E
    let := c.etale_η
    let := c.open_i
    let : IsOpenImmersion (SmoothSite.a1Map (.of L) c.i).left := by
      exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) c.open_i
        (inferInstanceAs (IsOpenImmersion (𝟙 (SmoothSite.affineLine (.of L)).left)))
        (MorphismProperty.Over.w c.i).symm (Category.id_comp _).symm
    let : Mono (SmoothSite.a1Map (.of L) c.i) :=
      (SmoothSite.forgetScheme _).mono_of_mono_map
        (inferInstanceAs (Mono (SmoothSite.a1Map (.of L) c.i).left))
    let : IsOpenImmersion δ.left := inferInstanceAs
      (IsOpenImmersion (pullback.fst W.hom (SmoothSite.contractionOpen (.of k) X).left))
    let : IsOpenImmersion (F.map δ).left := by
      let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
      have heq : (F.map δ).left = pullback.map _ f _ f δ.left (𝟙 _) (𝟙 _)
          (by simp only [Category.comp_id, MorphismProperty.Over.w])
          (by simp only [Category.comp_id, Category.id_comp]) := by
        apply pullback.hom_ext <;> simp [F, SmoothSite.fieldBaseChange,
          SmoothSite.baseChange_map_fst, SmoothSite.baseChange_map_snd,
          pullback.map, f]
      rw [heq]
      infer_instance
    let : Mono (F.map δ) := (SmoothSite.forgetScheme _).mono_of_mono_map
      (inferInstanceAs (Mono (F.map δ).left))
    have hb' : (F.map eU.inv ≫ b) ≫ c.i = F.map j' := by
      rw [Category.assoc, hb, ← Functor.map_comp]
    exact restrictScalarAffineWitness P j' q₀ qU r
      (SmoothSite.originalOpenRefinement_condition q₀ j') z₀ zU
      (SmoothSite.originalOpenRefinementZero_ambient q₀ j' z₀ hz₀) e₀ δ φU hφU
      c.i (F.map eU.inv ≫ b) hb' c.η c.q c.base_eq c.ζ c.mark_eq
      c.α c.β c.square c.φ c.ambient_eq d c.a c.c c.relation
  obtain ⟨a₁⟩ := restrict L₁ c₁ b₁ hb₁
  obtain ⟨a₂⟩ := restrict L₂ c₂ b₂ hb₂
  let := a₁.affine
  let := a₂.affine
  let := a₁.etale
  let := a₂.etale
  let : Algebra k Γ(YU.left, ⊤) := sectionsAlgebra YU
  let : Algebra Γ(YU.left, ⊤) Γ(U.left, ⊤) := zU.left.appTop.hom.toAlgebra
  have he : YU.left.isoSpec.inv ≫ YU.hom = Spec.algebraMap k Γ(YU.left, ⊤) :=
    isoSpec_inv_base YU
  have hchart : U.left.isoSpec.inv ≫ zU.left =
      Spec.algebraMap Γ(YU.left, ⊤) Γ(U.left, ⊤) ≫ YU.left.isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality zU.left).symm
  have hambient : (r ≫ e₀).left ≫ W.hom =
      qU.left ≫ ((cylinderNeighborhood X).obj V).hom := by
    have h := originalOpenRefinement_ambient X W v₀ j' q₀ e₀ hp
    rw [hbase] at h
    exact congrArg (fun f => f.left) h
  have hmarkU : zU.left ≫ (r ≫ e₀).left =
      v.left ≫ pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left := by
    have h := congrArg (fun f => f.left)
      (SmoothSite.originalOpenRefinementZero_ambient q₀ j' z₀ hz₀)
    change zU.left ≫ r.left = j'.left ≫ s₀ at h
    change zU.left ≫ (r.left ≫ e₀.left) = (U₀.ι ≫ v₀.left) ≫ _
    rw [← Category.assoc, h, Category.assoc, hmark]
    change (𝟙 _ ≫ U₀.ι) ≫ v₀.left ≫ _ = _
    simp only [Category.id_comp, Category.assoc]
  have hφ₂ : φU.left ≫ pullback.snd W.hom
      (SmoothSite.contractionOpen (.of k) X).left =
      (SmoothSite.etalePullbackSnd qU (SmoothSite.contractionOpen (.of k) U)).left ≫
        (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left := by
    have h := originalOpenRefinementToPunctured_snd X W v₀ j' q₀ e₀ hp
    rw [hbase] at h
    exact h
  refine ⟨V, v, inferInstance, originalOpenBaseToZero_retains X W v₀ j w
    ⟨⟨w, hwU⟩, rfl⟩, ?_⟩
  exact imageSieve_of_affine_weil_corrections
    (A := Γ(YU.left, ⊤)) (T := Γ(U.left, ⊤)) X P V YU qU zU
    (SmoothSite.originalOpenRefinementZero_cylinder q₀ j' z₀ hz₀)
    (r ≫ e₀) hambient v hmarkU YU.left.isoSpec.symm he U.left.isoSpec.symm hchart
    φU (originalOpenRefinementToPunctured_fst X W v₀ j' q₀ e₀ hp) hφ₂ d
    a₁.f a₁.mark a₁.mark_eq a₁.laurentSection a₁.ambientSection a₁.relation
    a₂.f a₂.mark a₂.mark_eq a₂.laurentSection a₂.ambientSection a₂.relation
    (by change (Module.finrank k L₁).Coprime (Module.finrank k L₂)
        rw [show Module.finrank k L₁ = n from hd₁, show Module.finrank k L₂ = m from hd₂]
        exact hnm)

end Motivic.FiniteEtaleSite.OriginalPresheaf
