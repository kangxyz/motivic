/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Triple fiber products of schemes
-/

@[expose] public noncomputable section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The triple product, retaining the two adjacent product factors. -/
noncomputable abbrev correspondenceTripleProduct : Scheme.{u} :=
  pullback (pullback.snd f g) (pullback.fst g h)

/-- The projection from the triple product to its first and last factors. -/
noncomputable def correspondenceTripleProjection :
    correspondenceTripleProduct f g h ⟶ pullback f h :=
  pullback.lift
    (pullback.fst (pullback.snd f g) (pullback.fst g h) ≫ pullback.fst f g)
    (pullback.snd (pullback.snd f g) (pullback.fst g h) ≫ pullback.snd g h) (by
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        pullback.condition])

@[reassoc (attr := simp)]
theorem correspondenceTripleProjection_fst :
    correspondenceTripleProjection f g h ≫ pullback.fst f h =
      pullback.fst (pullback.snd f g) (pullback.fst g h) ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceTripleProjection_snd :
    correspondenceTripleProjection f g h ≫ pullback.snd f h =
      pullback.snd (pullback.snd f g) (pullback.fst g h) ≫ pullback.snd g h :=
  pullback.lift_snd _ _ _


end AlgebraicGeometry.Scheme.Products
