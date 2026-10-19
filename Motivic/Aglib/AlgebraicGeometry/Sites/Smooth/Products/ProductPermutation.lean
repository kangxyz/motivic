/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products

/-! # Permuting the two parameters of literal relative products -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (X T U : SmoothSite S)

/-- Interchange the last two factors of actual relative scheme products. -/
def productSwapLast : product (product X T) U ⟶ product (product X U) T :=
  productLift
    (productLift (productFst (product X T) U ≫ productFst X T)
      (productSnd (product X T) U))
    (productFst (product X T) U ≫ productSnd X T)

/-- The displayed factor permutation is an actual smooth-scheme isomorphism. -/
def productSwapLastIso : product (product X T) U ≅ product (product X U) T where
  hom := productSwapLast X T U
  inv := productSwapLast X U T
  hom_inv_id := by
    apply product_hom_ext
    · apply product_hom_ext <;> simp [productSwapLast, Category.assoc]
    · simp [productSwapLast, Category.assoc]
  inv_hom_id := by
    apply product_hom_ext
    · apply product_hom_ext <;> simp [productSwapLast, Category.assoc]
    · simp [productSwapLast, Category.assoc]

/-- Forgetting the permuted parameter is exactly the original product projection. -/
@[reassoc (attr := simp)]
theorem productSwapLast_fst :
    productSwapLast X T U ≫ productFst (product X U) T =
      productMap (productFst X T) (𝟙 U) := by
  apply product_hom_ext <;> simp [productSwapLast]

/-- The retained homotopy coordinate is the original middle coordinate. -/
@[reassoc (attr := simp)]
theorem productSwapLast_snd :
    productSwapLast X T U ≫ productSnd (product X U) T =
      productFst (product X T) U ≫ productSnd X T := by
  simp [productSwapLast]

/-- The permutation commutes with the literal maps in all three factors. -/
theorem productSwapLast_naturality {X' T' U' : SmoothSite S}
    (f : X ⟶ X') (g : T ⟶ T') (h : U ⟶ U') :
    productMap (productMap f g) h ≫ productSwapLast X' T' U' =
      productSwapLast X T U ≫ productMap (productMap f h) g := by
  apply product_hom_ext
  · apply product_hom_ext <;> simp [productSwapLast, Category.assoc]
  · simp [productSwapLast, Category.assoc]

end AlgebraicGeometry.Scheme.SmoothSite
