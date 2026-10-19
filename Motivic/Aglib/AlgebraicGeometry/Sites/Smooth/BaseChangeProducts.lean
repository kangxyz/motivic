/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# Base change of relative products

Arbitrary base change identifies the base object and relative products with
those over the new base. The comparisons retain the literal scheme pullback
projections; no smoothness or finite-type assumption is made on the base map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S T : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false

/-- Base change of the base object is the new base, by the second pullback projection. -/
def baseChangeBaseIso (f : T ⟶ S) : (baseChange f).obj (base S) ≅ base T :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) f)) (by simp [base])

@[simp]
theorem baseChangeBaseIso_hom_left (f : T ⟶ S) :
    (baseChangeBaseIso f).hom.left = pullback.snd (𝟙 S) f := rfl

/-- Maps into a base-changed relative product are determined by the two projections. -/
theorem baseChange_product_hom_ext (f : T ⟶ S) {W : SmoothSite T} {X Y : SmoothSite S}
    {a b : W ⟶ (baseChange f).obj (product X Y)}
    (h₁ : a ≫ (baseChange f).map (productFst X Y) =
      b ≫ (baseChange f).map (productFst X Y))
    (h₂ : a ≫ (baseChange f).map (productSnd X Y) =
      b ≫ (baseChange f).map (productSnd X Y)) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [MorphismProperty.Comma.comp_left, Category.assoc,
        baseChange_map_fst, productFst, homMk_left] using
        congrArg (fun k => k.left ≫ pullback.fst X.hom f) h₁
    · simpa only [MorphismProperty.Comma.comp_left, Category.assoc,
        baseChange_map_fst, productSnd, homMk_left] using
        congrArg (fun k => k.left ≫ pullback.fst Y.hom f) h₂
  · exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm

/-- The canonical lift to the base change of the original relative product. -/
def baseChangeProductLift (f : T ⟶ S) {W : SmoothSite T} {X Y : SmoothSite S}
    (a : W ⟶ (baseChange f).obj X) (b : W ⟶ (baseChange f).obj Y) :
    W ⟶ (baseChange f).obj (product X Y) :=
  homMk (pullback.lift
    (pullback.lift (a.left ≫ pullback.fst X.hom f) (b.left ≫ pullback.fst Y.hom f)
      (by
        simp only [Category.assoc, pullback.condition]
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (fun k => k ≫ f)
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)))
    W.hom (by
      change _ ≫ pullback.fst X.hom Y.hom ≫ X.hom = _
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, pullback.condition,
        ← Category.assoc]
      exact congrArg (fun k => k ≫ f) (MorphismProperty.Over.w a)))
    (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
theorem baseChangeProductLift_fst (f : T ⟶ S) {W : SmoothSite T} {X Y : SmoothSite S}
    (a : W ⟶ (baseChange f).obj X) (b : W ⟶ (baseChange f).obj Y) :
    baseChangeProductLift f a b ≫ (baseChange f).map (productFst X Y) = a := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [Category.assoc, baseChangeProductLift,
      productFst, baseChange_map_fst]
  · exact (MorphismProperty.Over.w
      (baseChangeProductLift f a b ≫ (baseChange f).map (productFst X Y))).trans
        (MorphismProperty.Over.w a).symm

@[reassoc (attr := simp)]
theorem baseChangeProductLift_snd (f : T ⟶ S) {W : SmoothSite T} {X Y : SmoothSite S}
    (a : W ⟶ (baseChange f).obj X) (b : W ⟶ (baseChange f).obj Y) :
    baseChangeProductLift f a b ≫ (baseChange f).map (productSnd X Y) = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [Category.assoc, baseChangeProductLift,
      productSnd, baseChange_map_fst]
  · exact (MorphismProperty.Over.w
      (baseChangeProductLift f a b ≫ (baseChange f).map (productSnd X Y))).trans
        (MorphismProperty.Over.w b).symm

/-- Arbitrary base change commutes with the actual relative scheme product. -/
def baseChangeProductIso (f : T ⟶ S) (X Y : SmoothSite S) :
    (baseChange f).obj (product X Y) ≅
      product ((baseChange f).obj X) ((baseChange f).obj Y) where
  hom := productLift ((baseChange f).map (productFst X Y))
    ((baseChange f).map (productSnd X Y))
  inv := baseChangeProductLift f (productFst _ _) (productSnd _ _)
  hom_inv_id := by
    apply baseChange_product_hom_ext f <;> simp
  inv_hom_id := by
    apply product_hom_ext <;> simp

@[reassoc (attr := simp)]
theorem baseChangeProductIso_hom_fst (f : T ⟶ S) (X Y : SmoothSite S) :
    (baseChangeProductIso f X Y).hom ≫
      productFst ((baseChange f).obj X) ((baseChange f).obj Y) =
        (baseChange f).map (productFst X Y) :=
  productLift_fst _ _

@[reassoc (attr := simp)]
theorem baseChangeProductIso_hom_snd (f : T ⟶ S) (X Y : SmoothSite S) :
    (baseChangeProductIso f X Y).hom ≫
      productSnd ((baseChange f).obj X) ((baseChange f).obj Y) =
        (baseChange f).map (productSnd X Y) :=
  productLift_snd _ _

@[reassoc (attr := simp)]
theorem baseChangeProductIso_inv_fst (f : T ⟶ S) (X Y : SmoothSite S) :
    (baseChangeProductIso f X Y).inv ≫ (baseChange f).map (productFst X Y) =
      productFst ((baseChange f).obj X) ((baseChange f).obj Y) :=
  baseChangeProductLift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeProductIso_inv_snd (f : T ⟶ S) (X Y : SmoothSite S) :
    (baseChangeProductIso f X Y).inv ≫ (baseChange f).map (productSnd X Y) =
      productSnd ((baseChange f).obj X) ((baseChange f).obj Y) :=
  baseChangeProductLift_snd _ _ _

/-- Isomorphisms of factors induce the literal relative product isomorphism. -/
def productIso {X X' Y Y' : SmoothSite S} (a : X ≅ X') (b : Y ≅ Y') :
    product X Y ≅ product X' Y' where
  hom := productMap a.hom b.hom
  inv := productMap a.inv b.inv
  hom_inv_id := by rw [← productMap_comp]; simp
  inv_hom_id := by rw [← productMap_comp]; simp

@[simp]
theorem productIso_hom {X X' Y Y' : SmoothSite S} (a : X ≅ X') (b : Y ≅ Y') :
    (productIso a b).hom = productMap a.hom b.hom := rfl

@[simp]
theorem productIso_inv {X X' Y Y' : SmoothSite S} (a : X ≅ X') (b : Y ≅ Y') :
    (productIso a b).inv = productMap a.inv b.inv := rfl

/-- The two actual product projections make the base-change comparison natural. -/
@[reassoc]
theorem baseChangeProductIso_naturality {S T : Scheme.{u}} (f : T ⟶ S)
    {X X' Y Y' : SmoothSite S} (a : X ⟶ X') (b : Y ⟶ Y') :
    (baseChange f).map (productMap a b) ≫ (baseChangeProductIso f X' Y').hom =
      (baseChangeProductIso f X Y).hom ≫
        productMap ((baseChange f).map a) ((baseChange f).map b) := by
  apply product_hom_ext
  · simp [← Functor.map_comp]
  · simp [← Functor.map_comp]

end AlgebraicGeometry.Scheme.SmoothSite
