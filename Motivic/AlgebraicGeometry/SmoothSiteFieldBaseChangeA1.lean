/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteForgetBaseA1
public import Motivic.AlgebraicGeometry.SmoothSiteTorusBaseChange
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionGeometry

/-! # Original field-change cylinder, zero-section and Laurent-open comparisons -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.SmoothSite

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

local notation "r" => finiteSeparableBaseMap k L
local notation "c" => CommRingCat.ofHom (algebraMap k L)
local notation "B" => baseChange r

/-- The affine-line comparison uses the original polynomial Cartesian square. -/
def fieldBaseChangeAffineLineIso :
    (B).obj (affineLine (.of k)) ≅ affineLine (.of L) :=
  (MorphismProperty.Over.isoMk (finiteSeparablePolynomial_isPullback k L).flip.isoPullback
    (finiteSeparablePolynomial_isPullback k L).flip.isoPullback_hom_snd).symm

@[reassoc (attr := simp)]
theorem fieldBaseChangeAffineLineIso_inv_fst :
    (fieldBaseChangeAffineLineIso (k := k) (L := L)).inv.left ≫
      pullback.fst (polynomialProjection (.of k)) r =
        Spec.map (CommRingCat.PolynomialLaurent.polynomialMap c) :=
  (finiteSeparablePolynomial_isPullback k L).flip.isoPullback_hom_fst

/-- The native cylinder is the base change of the original cylinder, with unchanged factors. -/
def fieldBaseChangeA1Iso (X : SmoothSite (Spec (.of k))) :
    (B).obj (a1Cylinder (.of k) X) ≅ a1Cylinder (.of L) ((B).obj X) :=
  baseChangeProductIso r X (affineLine (.of k)) ≪≫
    productIso (Iso.refl _) fieldBaseChangeAffineLineIso

@[reassoc (attr := simp)]
theorem fieldBaseChangeA1Iso_projection (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeA1Iso (L := L) X).hom ≫ a1Projection (.of L) ((B).obj X) =
      (B).map (a1Projection (.of k) X) := by
  simp [fieldBaseChangeA1Iso, a1Projection]

@[reassoc (attr := simp)]
theorem fieldBaseChangeA1Iso_snd (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeA1Iso (L := L) X).hom ≫ productSnd ((B).obj X) (affineLine (.of L)) =
      (B).map (productSnd X (affineLine (.of k))) ≫ fieldBaseChangeAffineLineIso.hom := by
  simp [fieldBaseChangeA1Iso]

/-- Actual polynomial evaluation at zero commutes with the scalar map. -/
theorem polynomialZero_coefficient :
    (affineLinePoint (.of L) 0).left ≫
        Spec.map (CommRingCat.PolynomialLaurent.polynomialMap c) =
      r ≫ (affineLinePoint (.of k) 0).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro x
    simp [CommRingCat.PolynomialLaurent.polynomialMap]
  · simp [CommRingCat.PolynomialLaurent.polynomialMap]

/-- The comparison preserves the literal zero point. -/
@[reassoc]
theorem fieldBaseChangeAffineLineIso_zero :
    (B).map (affineLinePoint (.of k) 0) ≫ fieldBaseChangeAffineLineIso.hom =
      (baseChangeBaseIso r).hom ≫ affineLinePoint (.of L) 0 := by
  apply (cancel_mono (fieldBaseChangeAffineLineIso (k := k) (L := L)).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, affineLine_hom,
      fieldBaseChangeAffineLineIso_inv_fst]
    erw [baseChange_map_fst]
    change pullback.fst (𝟙 _) r ≫ (affineLinePoint (.of k) 0).left =
      pullback.snd (𝟙 _) r ≫ (affineLinePoint (.of L) 0).left ≫ _
    rw [polynomialZero_coefficient, ← Category.assoc, ← pullback.condition]
    simp
  · simpa only [baseChange_obj_hom] using
      (MorphismProperty.Over.w ((B).map (affineLinePoint (.of k) 0))).trans
        (MorphismProperty.Over.w ((baseChangeBaseIso r).hom ≫
          affineLinePoint (.of L) 0 ≫ fieldBaseChangeAffineLineIso.inv)).symm

/-- The original zero section becomes the native zero section under the cylinder comparison. -/
@[reassoc]
theorem fieldBaseChangeA1Iso_zero (X : SmoothSite (Spec (.of k))) :
    (B).map (a1Section (.of k) X 0) ≫ (fieldBaseChangeA1Iso (L := L) X).hom =
      a1Section (.of L) ((B).obj X) 0 := by
  apply product_hom_ext
  · change (B).map (a1Section (.of k) X 0) ≫
      (fieldBaseChangeA1Iso (L := L) X).hom ≫ a1Projection (.of L) ((B).obj X) =
        a1Section (.of L) ((B).obj X) 0 ≫ a1Projection (.of L) ((B).obj X)
    simp only [fieldBaseChangeA1Iso_projection,
      ← Functor.map_comp, a1Section_projection]
    exact (B).map_id X
  · rw [Category.assoc, fieldBaseChangeA1Iso_snd, ← Category.assoc,
      ← Functor.map_comp]
    simp only [a1Section, productLift_snd, Functor.map_comp, Category.assoc]
    rw [fieldBaseChangeAffineLineIso_zero]
    rw [← Category.assoc]
    congr 1
    apply MorphismProperty.Over.Hom.ext
    exact baseChange_map_snd r (toBase (.of k) X)

/-- The punctured cylinder uses the already constructed Laurent coefficient comparison. -/
def fieldBaseChangeTorusCylinderIso (X : SmoothSite (Spec (.of k))) :
    (B).obj (torusCylinder (.of k) X) ≅ torusCylinder (.of L) ((B).obj X) :=
  baseChangeProductIso r X (torus (.of k)) ≪≫
    productIso (Iso.refl _) (torusBaseChangeIso c)

/-- The native Laurent-open inclusion agrees with the original base-changed inclusion. -/
@[reassoc]
theorem fieldBaseChangeAffineLineIso_torusInAffineLine :
    (B).map (torusInAffineLine (.of k)) ≫ fieldBaseChangeAffineLineIso.hom =
      (torusBaseChangeIso c).hom ≫ torusInAffineLine (.of L) := by
  apply (cancel_mono (fieldBaseChangeAffineLineIso (k := k) (L := L)).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, affineLine_hom,
      fieldBaseChangeAffineLineIso_inv_fst]
    erw [baseChange_map_fst]
    have h : (torusInAffineLine (.of L)).left ≫
        Spec.map (CommRingCat.PolynomialLaurent.polynomialMap c) =
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap c) ≫
        (torusInAffineLine (.of k)).left := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp,
        CommRingCat.PolynomialLaurent.toLaurent_naturality]
    rw [h, ← Category.assoc, torusBaseChangeIso_hom_coefficientMap]
    rfl
  · simpa only [baseChange_obj_hom] using
      (MorphismProperty.Over.w ((B).map (torusInAffineLine (.of k)))).trans
        (MorphismProperty.Over.w ((torusBaseChangeIso c).hom ≫
          torusInAffineLine (.of L) ≫ fieldBaseChangeAffineLineIso.inv)).symm

/-- The cylinder comparisons preserve the exact open used by the boundary construction. -/
@[reassoc]
theorem fieldBaseChangeA1Iso_contractionOpen (X : SmoothSite (Spec (.of k))) :
    (B).map (contractionOpen (.of k) X) ≫ (fieldBaseChangeA1Iso (L := L) X).hom =
      (fieldBaseChangeTorusCylinderIso (L := L) X).hom ≫
        contractionOpen (.of L) ((B).obj X) := by
  apply product_hom_ext
  · simp [fieldBaseChangeA1Iso, fieldBaseChangeTorusCylinderIso, contractionOpen,
      ← Functor.map_comp]
  · simp only [Category.assoc, fieldBaseChangeA1Iso_snd,
      fieldBaseChangeTorusCylinderIso, Iso.trans_hom, productIso_hom,
      contractionOpen, productMap_snd]
    rw [← Category.assoc, ← Functor.map_comp]
    simp only [productMap_snd, Functor.map_comp, Category.assoc]
    rw [fieldBaseChangeAffineLineIso_torusInAffineLine]
    simp only [productMap_snd_assoc, baseChangeProductIso_hom_snd_assoc]


end Motivic.SmoothSite
