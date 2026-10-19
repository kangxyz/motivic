/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Triple.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Ambient schemes for diagonal intersections
-/

@[expose] public noncomputable section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The product of the two adjacent products over the base scheme. -/
noncomputable abbrev correspondenceIntersectionAmbient : Scheme.{u} :=
  pullback (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)

/-- The actual map from the ambient space to the middle self-product. -/
noncomputable def correspondenceMiddlePair :
    correspondenceIntersectionAmbient f g h ⟶ pullback g g :=
  pullback.map (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) g g
    (pullback.snd f g) (pullback.fst g h) (𝟙 S) (by simp) (by simp)

/-- The triple product embeds by identifying the two middle coordinates. -/
noncomputable abbrev correspondenceTripleInclusion :
    correspondenceTripleProduct f g h ⟶ correspondenceIntersectionAmbient f g h :=
  pullback.mapDesc (pullback.snd f g) (pullback.fst g h) g

/-- The middle-coordinate map on the actual triple product. -/
noncomputable abbrev correspondenceTripleMiddle : correspondenceTripleProduct f g h ⟶ Y :=
  pullback.fst (pullback.snd f g) (pullback.fst g h) ≫ pullback.snd f g

/-- The actual triple-product inclusion is the base change of the middle diagonal. -/
theorem correspondenceTriple_isPullback :
    IsPullback (correspondenceTripleMiddle f g h) (correspondenceTripleInclusion f g h)
      (pullback.diagonal g) (correspondenceMiddlePair f g h) :=
  pullback_map_diagonal_isPullback (pullback.snd f g) (pullback.fst g h) g

instance [IsSeparated g] : IsClosedImmersion (correspondenceTripleInclusion f g h) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.mapDesc (pullback.snd f g) (pullback.fst g h) g))

set_option backward.isDefEq.respectTransparency false in
/-- Flat outer structure maps give the flat ambient base change of the diagonal. -/
instance [Flat f] [Flat h] : Flat (correspondenceMiddlePair f g h) := by
  unfold correspondenceMiddlePair
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat (pullback.snd f g)))
    (inferInstanceAs (Flat (pullback.fst g h))) rfl rfl

@[reassoc (attr := simp)]
theorem correspondenceMiddlePair_fst :
    correspondenceMiddlePair f g h ≫ pullback.fst g g =
      pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫ pullback.snd f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceMiddlePair_snd :
    correspondenceMiddlePair f g h ≫ pullback.snd g g =
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫ pullback.fst g h :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem correspondenceTripleInclusion_fst :
    correspondenceTripleInclusion f g h ≫
      pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) =
        pullback.fst (pullback.snd f g) (pullback.fst g h) := by
  simp only [correspondenceTripleInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem correspondenceTripleInclusion_snd :
    correspondenceTripleInclusion f g h ≫
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) =
        pullback.snd (pullback.snd f g) (pullback.fst g h) := by
  simp only [correspondenceTripleInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]


end AlgebraicGeometry.Scheme.Products
