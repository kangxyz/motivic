/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.IntersectionIdeal
public import Motivic.Aglib.AlgebraicGeometry.Products.Triple.Basic

/-!
# Ambient schemes for triple diagonals
-/

@[expose] public noncomputable section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- The last coordinate of the four-factor ambient scheme. -/
abbrev correspondenceAmbientTarget : correspondenceIntersectionAmbient f g h ⟶ Z :=
  pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫ pullback.snd g h

/-- The last coordinate after imposing the first middle diagonal. -/
abbrev correspondenceTripleTarget : correspondenceTripleProduct f g h ⟶ Z :=
  pullback.snd (pullback.snd f g) (pullback.fst g h) ≫ pullback.snd g h

/-- The actual product of the three adjacent two-factor ambient schemes. -/
abbrev correspondenceSixfoldAmbient : Scheme.{u} :=
  pullback (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)

/-- The first middle diagonal imposed in the six-factor ambient. -/
abbrev correspondenceFirstDiagonal : Scheme.{u} :=
  pullback (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)

/-- Both middle diagonals imposed, giving the actual fourfold product. -/
abbrev correspondenceFourfoldProduct : Scheme.{u} :=
  pullback (correspondenceTripleTarget f g h) (pullback.fst h i)

/-- The first diagonal inclusion is the exterior product of the original
middle-diagonal inclusion with the identity of the last adjacent product. -/
def correspondenceFirstDiagonalInclusion : correspondenceFirstDiagonal f g h i ⟶
    correspondenceSixfoldAmbient f g h i :=
  pullback.map _ _ _ _ (correspondenceTripleInclusion f g h) (𝟙 _) (𝟙 S)
    (by simp [correspondenceTripleTarget, correspondenceAmbientTarget]) (by simp)

set_option backward.isDefEq.respectTransparency false in
instance [IsSeparated g] : IsClosedImmersion (correspondenceFirstDiagonalInclusion f g h i) := by
  unfold correspondenceFirstDiagonalInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (correspondenceTripleInclusion f g h)))
    (inferInstanceAs (IsClosedImmersion (𝟙 (pullback h i)))) (by simp) (by simp)

/-- The second diagonal inclusion identifies the two remaining Z coordinates. -/
abbrev correspondenceSecondDiagonalInclusion : correspondenceFourfoldProduct f g h i ⟶
    correspondenceFirstDiagonal f g h i :=
  pullback.mapDesc (correspondenceTripleTarget f g h) (pullback.fst h i) h

instance [IsSeparated h] : IsClosedImmersion (correspondenceSecondDiagonalInclusion f g h i) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.mapDesc (correspondenceTripleTarget f g h) (pullback.fst h i) h))

/-- The first diagonal keeps the original triple-product coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceFirstDiagonalInclusion_fst :
    correspondenceFirstDiagonalInclusion f g h i ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
      correspondenceTripleInclusion f g h := pullback.lift_fst _ _ _

/-- The first diagonal keeps the last adjacent-product coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceFirstDiagonalInclusion_snd :
    correspondenceFirstDiagonalInclusion f g h i ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) := by
  simp only [correspondenceFirstDiagonalInclusion, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- The second diagonal keeps the first three coordinates. -/
@[reassoc (attr := simp)] theorem correspondenceSecondDiagonalInclusion_fst :
    correspondenceSecondDiagonalInclusion f g h i ≫
      pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondDiagonalInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The second diagonal keeps the last adjacent product. -/
@[reassoc (attr := simp)] theorem correspondenceSecondDiagonalInclusion_snd :
    correspondenceSecondDiagonalInclusion f g h i ≫
      pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (correspondenceTripleTarget f g h) (pullback.fst h i) := by
  simp only [correspondenceSecondDiagonalInclusion, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]


end AlgebraicGeometry.Scheme.Products
