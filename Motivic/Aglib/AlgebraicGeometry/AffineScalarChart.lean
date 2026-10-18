/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineScalarPullback

/-!
# Constructed scalar charts of original affine schemes and whole markings

Only original affine charts are inputs. Every scalar chart is constructed by
actual pullback maps and the canonical tensor-product comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable {W : Scheme.{u}} (w : W ⟶ Spec (.of R)) (e : Spec (.of A) ≅ W)
variable (he : e.hom ≫ w = Spec.algebraMap R A)

/-- The actual tensor affine chart of the original scalar extension. -/
def affineScalarChart : Spec (.of (A ⊗[R] B)) ≅ pullback w (Spec.algebraMap R B) :=
  (pullbackSpecIso R A B).symm ≪≫
    asIso (pullback.map (Spec.algebraMap R A) (Spec.algebraMap R B)
      w (Spec.algebraMap R B) e.hom (𝟙 _) (𝟙 _)
      (by simpa using he.symm) (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The scalar chart retains the entire original ambient projection. -/
@[reassoc (attr := simp)]
theorem affineScalarChart_hom_fst :
    (affineScalarChart R A B w e he).hom ≫ pullback.fst w (Spec.algebraMap R B) =
      Spec.algebraMap A (A ⊗[R] B) ≫ e.hom := by
  simp [affineScalarChart, pullback.map, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The scalar chart retains the actual ground-extension projection. -/
@[reassoc (attr := simp)]
theorem affineScalarChart_hom_snd :
    (affineScalarChart R A B w e he).hom ≫ pullback.snd w (Spec.algebraMap R B) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B)) := by
  simp [affineScalarChart, pullback.map, Category.assoc]

/-- The inverse chart also remembers the original affine-coordinate projection. -/
@[reassoc]
theorem affineScalarChart_inv_fst :
    (affineScalarChart R A B w e he).inv ≫ Spec.algebraMap A (A ⊗[R] B) =
      pullback.fst w (Spec.algebraMap R B) ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← affineScalarChart_hom_fst R A B w e he, Iso.inv_hom_id_assoc]

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))

/-- Pullback of the constructed scalar chart, retaining an arbitrary original source. -/
def affineScalarChartPullbackIso :
    pullback ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B) ≅
      pullback p (Spec.algebraMap A (A ⊗[R] B)) :=
  pullback.congrHom (by simp only [Category.assoc, he]) rfl ≪≫
    affineScalarPullbackIso R A B p

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back the chart leaves the original source projection unchanged. -/
@[reassoc (attr := simp)]
theorem affineScalarChartPullbackIso_hom_fst :
    (affineScalarChartPullbackIso R A B w e he p).hom ≫
        pullback.fst p (Spec.algebraMap A (A ⊗[R] B)) =
      pullback.fst ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B) := by
  simp [affineScalarChartPullbackIso, pullback.congrHom, pullback.map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back the chart leaves the extension scalar unchanged. -/
@[reassoc]
theorem affineScalarChartPullbackIso_hom_scalar :
    (affineScalarChartPullbackIso R A B w e he p).hom ≫
        pullback.snd p (Spec.algebraMap A (A ⊗[R] B)) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B)) =
      pullback.snd ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B) := by
  simp only [affineScalarChartPullbackIso, Iso.trans_hom, Category.assoc]
  rw [affineScalarPullbackIso_hom_scalar R A B p]
  simp [pullback.congrHom, pullback.map]

set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back scalar chart preserves the original ambient map, not only its base. -/
theorem affineScalarChartPullbackIso_ambient :
    (affineScalarChartPullbackIso R A B w e he p).hom ≫
      pullback.snd p (Spec.algebraMap A (A ⊗[R] B)) ≫
        (affineScalarChart R A B w e he).hom =
      pullback.map ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B)
        w (Spec.algebraMap R B) (p ≫ e.hom) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, affineScalarChart_hom_fst, pullback.map, pullback.lift_fst]
    rw [← Category.assoc (pullback.snd _ _) (Spec.algebraMap A (A ⊗[R] B)),
      ← pullback.condition]
    simp only [Category.assoc, affineScalarChartPullbackIso_hom_fst_assoc]
  · simp only [Category.assoc, affineScalarChart_hom_snd, pullback.map,
      pullback.lift_snd, Category.comp_id]
    exact affineScalarChartPullbackIso_hom_scalar R A B w e he p

variable {T : Type u} [CommRing T] [Algebra A T]
variable {V : Scheme.{u}} (v : V ⟶ Spec (.of R)) (d : Spec (.of T) ≅ V)
variable (hd : d.hom ≫ v = Spec.algebraMap A T ≫ Spec.algebraMap R A)

/-- The entire relative scalar marking domain has its constructed original scalar chart. -/
def relativeAffineScalarChart :
    pullback (Spec.algebraMap A T) (Spec.algebraMap A (A ⊗[R] B)) ≅
      pullback v (Spec.algebraMap R B) :=
  (affineScalarPullbackIso R A B (Spec.algebraMap A T)).symm ≪≫
    asIso (pullback.map (Spec.algebraMap A T ≫ Spec.algebraMap R A)
      (Spec.algebraMap R B) v (Spec.algebraMap R B) d.hom (𝟙 _) (𝟙 _)
      (by simpa using hd.symm) (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The relative marking chart preserves the complete original marked scheme. -/
@[reassoc]
theorem relativeAffineScalarChart_hom_fst :
    (relativeAffineScalarChart R A B v d hd).hom ≫
        pullback.fst v (Spec.algebraMap R B) =
      pullback.fst (Spec.algebraMap A T) (Spec.algebraMap A (A ⊗[R] B)) ≫ d.hom := by
  simp only [relativeAffineScalarChart, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    pullback.map, Category.assoc, pullback.lift_fst]
  rw [← affineScalarPullbackIso_hom_fst R A B (Spec.algebraMap A T)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The relative marking chart preserves the original extension scalar. -/
@[reassoc]
theorem relativeAffineScalarChart_hom_snd :
    (relativeAffineScalarChart R A B v d hd).hom ≫
        pullback.snd v (Spec.algebraMap R B) =
      pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A (A ⊗[R] B)) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B)) := by
  simp only [relativeAffineScalarChart, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [← affineScalarPullbackIso_hom_scalar R A B (Spec.algebraMap A T)]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A whole original marking is preserved by the two constructed scalar charts. -/
theorem relativeAffineScalarChart_ambient (z : V ⟶ W) (hz : v = z ≫ w)
    (hmark : d.hom ≫ z = Spec.algebraMap A T ≫ e.hom) :
    (relativeAffineScalarChart R A B v d hd).hom ≫
      pullback.map v (Spec.algebraMap R B) w (Spec.algebraMap R B)
        z (𝟙 _) (𝟙 _) (by simpa using hz) (by simp) =
      pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A (A ⊗[R] B)) ≫
        (affineScalarChart R A B w e he).hom := by
  apply pullback.hom_ext
  · simp only [pullback.map, Category.assoc, pullback.lift_fst,
      relativeAffineScalarChart_hom_fst_assoc, affineScalarChart_hom_fst]
    rw [hmark, ← Category.assoc, pullback.condition]
    simp only [Category.assoc]
  · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id,
      relativeAffineScalarChart_hom_snd, affineScalarChart_hom_snd]

end AlgebraicGeometry
