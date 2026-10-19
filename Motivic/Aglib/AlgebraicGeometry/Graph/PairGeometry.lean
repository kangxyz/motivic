/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.Morphism

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.IntersectionAmbient

/-!
# Geometry of graph pairs
-/

@[expose] public noncomputable section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S U Y : Scheme.{u}} (φ : U ⟶ Y) (g : Y ⟶ S)

/-- The actual product map induced by a map on the first factor and identity on the second. -/
noncomputable def graphMiddlePair : pullback (φ ≫ g) g ⟶ pullback g g :=
  pullback.map (φ ≫ g) g g g φ (𝟙 Y) (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem graphMiddlePair_fst :
    graphMiddlePair φ g ≫ pullback.fst g g = pullback.fst (φ ≫ g) g ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphMiddlePair_snd :
    graphMiddlePair φ g ≫ pullback.snd g g = pullback.snd (φ ≫ g) g := by
  simp only [graphMiddlePair, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The actual graph maps to the middle diagonal. -/
@[reassoc]
theorem correspondenceGraph_middlePair :
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g ≫ graphMiddlePair φ g = φ ≫
      pullback.diagonal g := by
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.Scheme.Products
