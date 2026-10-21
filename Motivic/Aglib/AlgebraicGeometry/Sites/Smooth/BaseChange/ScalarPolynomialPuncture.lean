/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Presentations.ScalarPolynomialCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.PuncturedCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.ContractionNaturality

/-! # Scalar polynomial coordinates retain the literal puncture

The actual scalar basic open is compared through the original Laurent product.
The original ambient map is preserved, not merely its open support.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.Smooth k R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The smoothness instance used in this module. -/
local instance scalarPolynomialPunctureSmooth1 : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

/-- The smoothness instance used in this module. -/
local instance scalarPolynomialPunctureSmooth2 : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

/-- The smoothness instance used in this module. -/
local instance scalarPolynomialPunctureSmooth3 : Algebra.Smooth L ((Polynomial R) ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L (Polynomial R))

/-- The actual scalar puncture is the original polynomial basic open over the
scalar coefficient algebra, with its Laurent factor unchanged. -/
def scalarPunctureIso :
    (fieldBaseChange (algebraMap k L)).obj
      (openSite (k := k) (Polynomial.X : Polynomial R)) ≅
        openSite (k := L) (Polynomial.X : Polynomial (R ⊗[k] L)) :=
  (fieldBaseChange (algebraMap k L)).mapIso puncturedProductIso ≪≫
    fieldBaseChangeTorusCylinderIso (affineSite k R) ≪≫
      productIso (affineScalarIso k R L) (Iso.refl _) ≪≫
        puncturedProductIso.symm

/-- Both scalar coordinate comparisons preserve the literal puncture inclusion. -/
@[reassoc]
theorem scalarPunctureIso_open :
    (fieldBaseChange (algebraMap k L)).map
        (openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫
      (scalarLineIso k R L).hom =
    (scalarPunctureIso k R L).hom ≫
      openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L)) := by
  apply (cancel_mono (lineCylinderIso (k := L) (R := R ⊗[k] L)).hom).mp
  simp only [scalarLineIso, scalarPunctureIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Functor.map_comp_assoc, ← puncturedProductIso_open, Functor.map_comp]
  have h := fieldBaseChangeA1Iso_contractionOpen (L := L) (affineSite k R)
  change (fieldBaseChange (algebraMap k L)).map
      (contractionOpen (.of k) (affineSite k R)) ≫
        (fieldBaseChangeA1Iso (L := L) (affineSite k R)).hom = _ at h
  rw [Category.assoc, ← Category.assoc _ _ (cylinderIso _).hom, h]
  change _ = _ ≫ _ ≫ _ ≫ (puncturedProductIso (k := L) (R := R ⊗[k] L)).inv ≫
    openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L)) ≫
      (lineCylinderIso (k := L) (R := R ⊗[k] L)).hom
  rw [← puncturedProductIso_open]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc, cylinderIso, productIso_hom,
    Iso.refl_hom, contractionOpen_naturality]

/-- The tensor coordinates and native scalar coordinates give exactly the same
original map, including for the original étale input and puncture. -/
@[reassoc]
theorem tensorPolynomialLineIso_map {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R)) :
    (fieldBaseChange (algebraMap k L)).map (p ≫ (polynomialAffineIso k R).hom) ≫
      (affineScalarIso k (Polynomial R) L).hom ≫
        (tensorPolynomialLineIso k R L).hom =
    (fieldBaseChange (algebraMap k L)).map p ≫ (scalarLineIso k R L).hom := by
  simp only [tensorPolynomialLineIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
