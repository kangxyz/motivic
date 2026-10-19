/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Coproducts

/-! # Consumers of the actual smooth-site disjoint union -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.SmoothSiteCoproducts

variable {S : Scheme.{u}} {W X Y Z : SmoothSite S}

example : HasBinaryCoproducts (SmoothSite S) := inferInstance

example : (SmoothSite.coproduct X Y).left = (X.left ⨿ Y.left) := rfl

example : (SmoothSite.coproduct X Y).hom = coprod.desc X.hom Y.hom := rfl

example : Smooth (SmoothSite.coproduct X Y).hom := inferInstance

example : IsSeparated (SmoothSite.coproduct X Y).hom := inferInstance

example : QuasiCompact (SmoothSite.coproduct X Y).hom := inferInstance

example : (SmoothSite.coproductInl X Y).left = coprod.inl := rfl

example : (SmoothSite.coproductInr X Y).left = coprod.inr := rfl

example : IsOpenImmersion (SmoothSite.coproductInl X Y).left := inferInstance

example : IsOpenImmersion (SmoothSite.coproductInr X Y).left := inferInstance

example : IsClosedImmersion (SmoothSite.coproductInl X Y).left := inferInstance

example : IsClosedImmersion (SmoothSite.coproductInr X Y).left := inferInstance

example : IsFinite (SmoothSite.coproductInl X Y).left := inferInstance

example : IsFinite (SmoothSite.coproductInr X Y).left := inferInstance

example {C : Set (SmoothSite.coproduct X Y).left}
    (hC : C ∈ irreducibleComponents (SmoothSite.coproduct X Y).left) :
    C ⊆ Set.range (SmoothSite.coproductInl X Y).left ∨
      C ⊆ Set.range (SmoothSite.coproductInr X Y).left :=
  SmoothSite.irreducibleComponent_subset_coproduct_range X Y hC

example {C : Set (SmoothSite.coproduct X Y).left}
    (hC : C ∈ irreducibleComponents (SmoothSite.coproduct X Y).left) :
    ¬ (C ⊆ Set.range (SmoothSite.coproductInl X Y).left ∧
      C ⊆ Set.range (SmoothSite.coproductInr X Y).left) :=
  SmoothSite.irreducibleComponent_not_subset_both_coproduct_ranges X Y hC

example (f : X ⟶ W) (g : Y ⟶ W) :
    SmoothSite.coproductInl X Y ≫ SmoothSite.coproductDesc f g = f := by simp

example (f : X ⟶ W) (g : Y ⟶ W) :
    SmoothSite.coproductInr X Y ≫ SmoothSite.coproductDesc f g = g := by simp

example (f : W ⟶ X) (g : X ⟶ Y) :
    SmoothSite.coproductMap (f ≫ g) (𝟙 Z) =
      SmoothSite.coproductMap f (𝟙 Z) ≫ SmoothSite.coproductMap g (𝟙 Z) := by
  simpa only [Category.id_comp] using SmoothSite.coproductMap_comp f g (𝟙 Z) (𝟙 Z)

example : IsColimit
    (BinaryCofan.mk (SmoothSite.coproductInl X Y) (SmoothSite.coproductInr X Y)) :=
  SmoothSite.coproductIsColimit X Y

example : coprod.inl ≫ (SmoothSite.categoricalCoproductIso X Y).hom =
    SmoothSite.coproductInl X Y := by simp

example (f : W ⟶ X) (g : Y ⟶ Z) :
    coprod.map f g ≫ (SmoothSite.categoricalCoproductIso X Z).hom =
      (SmoothSite.categoricalCoproductIso W Y).hom ≫ SmoothSite.coproductMap f g :=
  SmoothSite.categoricalCoproductIso_naturality f g

end MotivicTest.SmoothSiteCoproducts
