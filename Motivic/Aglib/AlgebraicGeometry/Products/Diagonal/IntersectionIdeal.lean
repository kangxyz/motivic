/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Kernel
public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.IntersectionAmbient

/-!
# Ideals of diagonal intersections
-/

@[expose] public noncomputable section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products
open _root_.AlgebraicGeometry.Scheme.Hom
/-- The triple-product ideal is the pullback of the actual middle-diagonal ideal. -/
theorem ker_correspondenceTripleInclusion {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) [IsSeparated g] :
    (correspondenceTripleInclusion f g h).ker =
      (pullback.diagonal g).ker.comap (correspondenceMiddlePair f g h) :=
  ker_eq_comap_of_isPullback _ _ _ _ (correspondenceTriple_isPullback f g h).flip


end AlgebraicGeometry.Scheme.Products
