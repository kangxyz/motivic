/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPolynomialBaseChange
public import Mathlib.RingTheory.Smooth.Basic

/-! # Native scalar pullbacks in the actual affine tensor coordinates

The comparison uses the canonical Spec tensor-product isomorphism. Both the
extension-field map and the original affine projection are unchanged.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.AffineTorusPolynomialPresentation
open scoped TensorProduct

universe u

namespace Motivic.SmoothSite

variable (k B L : Type u) [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra.Smooth k B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra.Smooth L (B ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)

/-- The actual scalar affine object is the spectrum of its literal tensor algebra. -/
def affineScalarIso :
    (fieldBaseChange (algebraMap k L)).obj (affineSite k B) ≅
      affineSite L (B ⊗[k] L) :=
  MorphismProperty.Over.isoMk (pullbackSpecIso k B L)
    (pullbackSpecIso_hom_snd k B L)

@[simp]
theorem affineScalarIso_hom_left :
    (affineScalarIso k B L).hom.left = (pullbackSpecIso k B L).hom := rfl

@[simp]
theorem affineScalarIso_inv_left :
    (affineScalarIso k B L).inv.left = (pullbackSpecIso k B L).inv := rfl

/-- The affine coordinate comparison preserves the original scalar projection. -/
@[reassoc]
theorem affineScalarIso_hom_original :
    (affineScalarIso k B L).hom.left ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L))) =
        pullback.fst (baseMap k B)
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  pullbackSpecIso_hom_fst' k B L

/-- The inverse affine comparison has the same original scalar projection. -/
@[reassoc]
theorem affineScalarIso_inv_original :
    (affineScalarIso k B L).inv.left ≫
      pullback.fst (baseMap k B)
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L))) :=
  pullbackSpecIso_inv_fst' k B L

/-- The native scalar image of any original affine-target arrow is its actual
Cartesian pullback in tensor coordinates. -/
theorem affineScalarMap_isPullback
    {Y : SmoothSite (Spec (.of k))} (p : Y ⟶ affineSite k B) :
    IsPullback
      (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (((fieldBaseChange (algebraMap k L)).map p).left ≫
        (affineScalarIso k B L).hom.left)
      p.left (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let F := fieldBaseChange (algebraMap k L)
  have Hbig : IsPullback
      ((F.map p).left ≫ (F.obj (affineSite k B)).hom)
      (pullback.fst Y.hom f) f (p.left ≫ (affineSite k B).hom) := by
    simpa only [F, f, fieldBaseChange, MorphismProperty.Over.w] using
      (baseChange_isPullback f Y).flip
  have H := (IsPullback.of_right Hbig
    (baseChange_map_fst f p) (baseChange_isPullback f (affineSite k B)).flip).flip
  let e := (forgetScheme (Spec (.of L))).mapIso (affineScalarIso k B L)
  apply H.of_iso' (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
  · rfl
  · change 𝟙 _ ≫ (F.map p).left =
      ((F.map p).left ≫ e.hom) ≫ e.inv
    simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simp
  · change (affineScalarIso k B L).inv.left ≫
        pullback.fst (baseMap k B)
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L))) ≫ 𝟙 _
    simpa only [Category.comp_id] using affineScalarIso_inv_original k B L

end Motivic.SmoothSite
