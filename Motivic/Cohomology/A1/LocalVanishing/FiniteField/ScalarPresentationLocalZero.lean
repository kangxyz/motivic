/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Presentation.OriginalOpen
public import Motivic.Transfers.Presheaf.FiniteScalarLocalZero
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.ScalarCoordinates

/-! # Scalar presentation zeros on native full-fiber neighborhoods

The presentation stays on its actual tensor affine target. Only sections and
the resulting open are transported through the canonical scalar isomorphism.
A unique entire scalar fiber, not a chosen lift alone, gives marked retention.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.RelativeCurve
open scoped TensorProduct

universe u w

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k B L : Type u} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra.Smooth k B] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local instance : Algebra.Smooth L (B ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)

/-- A chosen actual scalar presentation gives a native scalar zero open retaining
all points above the original mark, when the entire scalar fiber is unique. -/
theorem exists_scalar_zero_open_of_affine_presentation
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (affineSite k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    {Y Z : Scheme.{u}} (p : Y ⟶ (affineSite L (B ⊗[k] L)).left)
    (z : Z ⟶ (affineSite L (B ⊗[k] L)).left) [IsClosedImmersion z] (s : Z ⟶ Y)
    (e : OriginalEtalePresentation L (affineSite L (B ⊗[k] L)).hom p
      (pullback.snd a.left (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))))
      z s y) :
    ∃ V : ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left.Opens,
      (finiteScalarProjection (E := L) (affineSite k B)).left ⁻¹' {x} ⊆
        (V : Set ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left) ∧
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (homMk (X := mk (V.ι ≫
          ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).hom))
          (Y := (fieldBaseChange (algebraMap k L)).obj (affineSite k B)) V.ι rfl))
        (transfer P ((Cor.graphFunctor k).map
          (fieldBaseChangeForgetProjection (L := L) (affineSite k B))) v) = 0 := by
  let F := fieldBaseChange (algebraMap k L)
  let Q := finiteSeparableExtension L P
  let X := affineSite k B
  let XS := affineSite L (B ⊗[k] L)
  let i := affineScalarIso k B L
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))
  let AS := mk (pullback.snd a.left ρ ≫ XS.hom)
  let aS : AS ⟶ XS := homMk (pullback.snd a.left ρ) rfl
  have : IsAffine XS.left := inferInstanceAs (IsAffine (Spec (.of (B ⊗[k] L))))
  have : IsAffine (affineSite k B).left := inferInstanceAs (IsAffine (Spec (.of B)))
  have : IsAffine ((𝟭 Scheme).obj A.left) := inferInstanceAs (IsAffine A.left)
  have : IsAffine AS.left := inferInstanceAs (IsAffine (pullback a.left ρ))
  have : IsOpenImmersion aS.left := inferInstanceAs (IsOpenImmersion (pullback.snd a.left ρ))
  let H := affineScalarMap_isPullback k B L a
  have hc : H.isoPullback.inv ≫ (F.map a).left ≫ i.hom.left = pullback.snd a.left ρ := by
    simpa only [Category.assoc] using H.isoPullback_inv_snd
  let c : AS ⟶ F.obj A := homMk H.isoPullback.inv (by
    change H.isoPullback.inv ≫ (F.obj A).hom = pullback.snd a.left ρ ≫ XS.hom
    rw [← MorphismProperty.Over.w (F.map a), ← MorphismProperty.Over.w i.hom]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ XS.hom) hc)
  have hca : c ≫ F.map a = aS ≫ i.inv := by
    apply (cancel_mono i.hom).mp
    apply MorphismProperty.Over.Hom.ext
    change (H.isoPullback.inv ≫ (F.map a).left) ≫ i.hom.left =
      (pullback.snd a.left ρ ≫ i.inv.left) ≫ i.hom.left
    have hi : i.inv.left ≫ i.hom.left = 𝟙 _ :=
      congrArg (fun f => f.left) i.inv_hom_id
    simp only [Category.assoc]
    erw [hi, Category.comp_id]
    simpa only [Category.assoc] using hc
  let vL := transfer P ((Cor.graphFunctor k).map
    (fieldBaseChangeForgetProjection (L := L) X)) v
  have hz : transfer Q ((Cor.graphFunctor L).map aS)
      (transfer Q ((Cor.graphFunctor L).map i.inv) vL) = 0 := by
    have h0 := native_scalar_restriction_eq_zero_of_restriction_eq_zero (L := L) P a v hv
    have ht := congrArg (transfer Q ((Cor.graphFunctor L).map c)) h0
    rw [map_zero] at ht
    rw [← ConcreteCategory.comp_apply, ← transfer_comp, ← Functor.map_comp,
      hca, Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] at ht
    exact ht
  let y₀ := i.inv.left y
  have hi : i.hom.left y₀ = y := congrArg (fun f => f.left y) i.inv_hom_id
  have e' : OriginalEtalePresentation L XS.hom p aS.left z s (i.hom.left y₀) := by
    rw [hi]
    exact e
  obtain ⟨V, _hV, hyV, hzero⟩ := e'.exists_zero_on_original_open_of_iso
    i p aS z s y₀ Q (finiteSeparableExtension_isA1Invariant L P hP) vL hz
  refine ⟨V, ?_, hzero⟩
  intro t ht
  have hproj := congrArg (fun f => f t) (affineScalarIso_hom_original k B L)
  have hpoint : PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) (i.hom.left t) = x := by
    exact hproj.trans ht
  have heq : t = y₀ := by
    have h := congrArg (fun q => i.inv.left q) (hunique _ hpoint)
    have hid := congrArg (fun f => f.left t) i.hom_inv_id
    exact hid.symm.trans h
  rwa [heq]

end Motivic.PresheafWithTransfers
