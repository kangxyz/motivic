/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products

/-! # Consumers of the actual relative smooth-site product -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.SmoothSiteProducts

variable {S : Scheme.{u}} {W X Y Z : SmoothSite S}

example : HasBinaryProducts (SmoothSite S) := inferInstance

example : (SmoothSite.product X Y).left = pullback X.hom Y.hom := rfl

example (f : W ⟶ X) (g : W ⟶ Y) :
    SmoothSite.productLift f g ≫ SmoothSite.productFst X Y = f := by simp

example (f : W ⟶ X) (g : W ⟶ Y) :
    SmoothSite.productLift f g ≫ SmoothSite.productSnd X Y = g := by simp

example (f : W ⟶ X) (g : X ⟶ Y) :
    SmoothSite.productMap (f ≫ g) (𝟙 Z) =
      SmoothSite.productMap f (𝟙 Z) ≫ SmoothSite.productMap g (𝟙 Z) := by
  simpa only [Category.id_comp] using SmoothSite.productMap_comp f g (𝟙 Z) (𝟙 Z)

example : IsLimit (BinaryFan.mk (SmoothSite.productFst X Y) (SmoothSite.productSnd X Y)) :=
  SmoothSite.productIsLimit X Y

example : (SmoothSite.categoricalProductIso X Y).hom ≫ SmoothSite.productFst X Y =
    prod.fst := by simp

example (f : W ⟶ X) (g : Y ⟶ Z) :
    prod.map f g ≫ (SmoothSite.categoricalProductIso X Z).hom =
      (SmoothSite.categoricalProductIso W Y).hom ≫ SmoothSite.productMap f g :=
  SmoothSite.categoricalProductIso_naturality f g

end MotivicTest.SmoothSiteProducts
