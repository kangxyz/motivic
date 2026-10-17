/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Relative products in the smooth category

The product is the literal scheme-theoretic fiber product over the specified
base. Its projections, maps and universal property are constructed in the
smooth category. This does not assert a categorical product in finite
correspondences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SmoothSite

variable {S : Scheme.{u}}

/-- The actual relative scheme product, with its smooth structure map. -/
def product (X Y : SmoothSite S) : SmoothSite S :=
  mk (pullback.fst X.hom Y.hom ≫ X.hom)

@[simp] theorem product_left (X Y : SmoothSite S) :
    (product X Y).left = pullback X.hom Y.hom := rfl

@[simp] theorem product_hom (X Y : SmoothSite S) :
    (product X Y).hom = pullback.fst X.hom Y.hom ≫ X.hom := rfl

/-- First relative product projection. -/
def productFst (X Y : SmoothSite S) : product X Y ⟶ X :=
  homMk (pullback.fst X.hom Y.hom) rfl

/-- Second relative product projection. -/
def productSnd (X Y : SmoothSite S) : product X Y ⟶ Y :=
  homMk (pullback.snd X.hom Y.hom) (pullback.condition.symm)

/-- The relative product lift retains the original two scheme maps. -/
def productLift {W X Y : SmoothSite S} (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ product X Y :=
  homMk (pullback.lift f.left g.left
    ((MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm))
    (by
      change _ ≫ pullback.fst X.hom Y.hom ≫ X.hom = W.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact MorphismProperty.Over.w f)

@[reassoc (attr := simp)]
theorem productLift_fst {W X Y : SmoothSite S} (f : W ⟶ X) (g : W ⟶ Y) :
    productLift f g ≫ productFst X Y = f := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem productLift_snd {W X Y : SmoothSite S} (f : W ⟶ X) (g : W ⟶ Y) :
    productLift f g ≫ productSnd X Y = g := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

/-- Maps into the actual relative product are determined by its two projections. -/
@[ext] theorem product_hom_ext {W X Y : SmoothSite S} {f g : W ⟶ product X Y}
    (h₁ : f ≫ productFst X Y = g ≫ productFst X Y)
    (h₂ : f ≫ productSnd X Y = g ≫ productSnd X Y) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.hom_ext (congrArg (fun a => a.left) h₁) (congrArg (fun a => a.left) h₂)

/-- The relative product acts on arbitrary smooth-site morphisms in both factors. -/
def productMap {X X' Y Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    product X Y ⟶ product X' Y' :=
  productLift (productFst X Y ≫ f) (productSnd X Y ≫ g)

@[reassoc (attr := simp)]
theorem productMap_fst {X X' Y Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    productMap f g ≫ productFst X' Y' = productFst X Y ≫ f := by
  simp [productMap]

@[reassoc (attr := simp)]
theorem productMap_snd {X X' Y Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    productMap f g ≫ productSnd X' Y' = productSnd X Y ≫ g := by
  simp [productMap]

@[simp] theorem productMap_id (X Y : SmoothSite S) :
    productMap (𝟙 X) (𝟙 Y) = 𝟙 (product X Y) := by
  apply product_hom_ext <;> simp

theorem productMap_comp {X X' X'' Y Y' Y'' : SmoothSite S}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    productMap (f ≫ f') (g ≫ g') = productMap f g ≫ productMap f' g' := by
  apply product_hom_ext <;> simp

/-- The literal relative product is a categorical binary product in the smooth site. -/
def productIsLimit (X Y : SmoothSite S) :
    IsLimit (BinaryFan.mk (productFst X Y) (productSnd X Y)) :=
  BinaryFan.isLimitMk (fun s => productLift s.fst s.snd)
    (fun s => productLift_fst s.fst s.snd)
    (fun s => productLift_snd s.fst s.snd)
    (fun _ _ h₁ h₂ => product_hom_ext (h₁.trans (productLift_fst _ _).symm)
      (h₂.trans (productLift_snd _ _).symm))

instance (X Y : SmoothSite S) : HasBinaryProduct X Y :=
  ⟨⟨_, productIsLimit X Y⟩⟩

instance : HasBinaryProducts (SmoothSite S) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- The chosen categorical product is canonically the literal relative scheme product. -/
def categoricalProductIso (X Y : SmoothSite S) : X ⨯ Y ≅ product X Y :=
  limit.isoLimitCone ⟨_, productIsLimit X Y⟩

@[reassoc (attr := simp)]
theorem categoricalProductIso_hom_fst (X Y : SmoothSite S) :
    (categoricalProductIso X Y).hom ≫ productFst X Y = prod.fst :=
  limit.isoLimitCone_hom_π ⟨_, productIsLimit X Y⟩ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem categoricalProductIso_hom_snd (X Y : SmoothSite S) :
    (categoricalProductIso X Y).hom ≫ productSnd X Y = prod.snd :=
  limit.isoLimitCone_hom_π ⟨_, productIsLimit X Y⟩ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
theorem categoricalProductIso_inv_fst (X Y : SmoothSite S) :
    (categoricalProductIso X Y).inv ≫ prod.fst = productFst X Y :=
  limit.isoLimitCone_inv_π ⟨_, productIsLimit X Y⟩ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem categoricalProductIso_inv_snd (X Y : SmoothSite S) :
    (categoricalProductIso X Y).inv ≫ prod.snd = productSnd X Y :=
  limit.isoLimitCone_inv_π ⟨_, productIsLimit X Y⟩ ⟨WalkingPair.right⟩

/-- Ordinary categorical product maps agree with the displayed relative scheme maps. -/
@[reassoc]
theorem categoricalProductIso_naturality {X X' Y Y' : SmoothSite S}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    prod.map f g ≫ (categoricalProductIso X' Y').hom =
      (categoricalProductIso X Y).hom ≫ productMap f g := by
  apply product_hom_ext <;> simp

end Motivic.SmoothSite
