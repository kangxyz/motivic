/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.IntersectionAmbient
public import Motivic.Aglib.AlgebraicGeometry.Graph.PairGeometry

/-!
# Geometry of left graph pairs
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S U Y : Scheme.{u}} (φ : U ⟶ Y) (g : Y ⟶ S)

/-- The transposed actual graph pair, retaining the original middle-coordinate order. -/
noncomputable def leftGraphMiddlePair : pullback (φ ≫ g) g ⟶ pullback g g :=
  graphMiddlePair φ g ≫ (pullbackSymmetry g g).hom

@[reassoc (attr := simp)]
theorem leftGraphMiddlePair_fst :
    leftGraphMiddlePair φ g ≫ pullback.fst g g = pullback.snd (φ ≫ g) g := by
  simp [leftGraphMiddlePair]

@[reassoc (attr := simp)]
theorem leftGraphMiddlePair_snd :
    leftGraphMiddlePair φ g ≫ pullback.snd g g = pullback.fst (φ ≫ g) g ≫ φ := by
  simp [leftGraphMiddlePair]

/-- The actual diagonal is fixed by the actual pullback symmetry. -/
@[reassoc (attr := simp)]
theorem diagonal_symmetry :
    pullback.diagonal g ≫ (pullbackSymmetry g g).hom = pullback.diagonal g := by
  apply pullback.hom_ext <;> simp

/-- A graph maps to the same diagonal after transposing the two middle coordinates. -/
@[reassoc]
theorem correspondenceGraph_leftMiddlePair :
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g ≫ leftGraphMiddlePair φ g = φ ≫
      pullback.diagonal g := by
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.Scheme.Products
