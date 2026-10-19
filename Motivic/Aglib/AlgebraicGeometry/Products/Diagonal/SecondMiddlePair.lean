/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.TripleIdeals

/-!
# Second middle pairs in scheme products
-/

@[expose] public noncomputable section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- The original second middle pair remembers the first Z coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSixfoldSecondMiddlePair_fst :
    correspondenceSixfoldSecondMiddlePair f g h i ≫ pullback.fst h h =
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
        correspondenceAmbientTarget f g h := pullback.lift_fst _ _ _

/-- The original second middle pair remembers the second Z coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSixfoldSecondMiddlePair_snd :
    correspondenceSixfoldSecondMiddlePair f g h i ≫ pullback.snd h h =
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
        pullback.fst h i := pullback.lift_snd _ _ _


end AlgebraicGeometry.Scheme.Products
