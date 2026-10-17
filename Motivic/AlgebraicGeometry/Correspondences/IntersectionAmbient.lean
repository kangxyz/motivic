/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.CompositionSupportEmbedding
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The actual ambient space for diagonal intersection

The ambient scheme is `(X ×[S] Y) ×[S] (Y ×[S] Z)`. The existing triple
product is its pullback along the actual diagonal of `Y → S`. Its structural
map to `Y ×[S] Y` is flat when the outer two structure maps are flat.
For correspondence generators the product of their support schemes has its
literal closed immersion into this ambient scheme. The actual incidence
scheme is the Cartesian intersection with the triple product. No reduced
structure, regularity of support modules, or intersection cycle is imposed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

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

namespace FiniteCorrespondenceGenerator

variable {f g h} (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The literal product of the two support schemes over the base. -/
noncomputable abbrev supportProduct : Scheme.{u} :=
  pullback (A.targetProjection ≫ g) (B.projection ≫ g)

/-- The product closed immersion in the ambient product of adjacent factors. -/
noncomputable def supportProductInclusion :
    A.supportProduct B ⟶ correspondenceIntersectionAmbient f g h :=
  pullback.map (A.targetProjection ≫ g) (B.projection ≫ g)
    (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)
    A.inclusion B.inclusion (𝟙 S)
    (by simp [targetProjection]) (by simp [projection, correspondenceProjection])

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (A.supportProductInclusion B) := by
  unfold supportProductInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion A.inclusion))
    (inferInstanceAs (IsClosedImmersion B.inclusion))
    (by simp [targetProjection]) (by simp [projection, correspondenceProjection])

/-- The actual incidence map to the product of the support schemes. -/
noncomputable abbrev incidenceToSupportProduct : A.incidence B ⟶ A.supportProduct B :=
  pullback.mapDesc A.targetProjection B.projection g

instance [IsSeparated g] : IsClosedImmersion (A.incidenceToSupportProduct B) :=
  inferInstanceAs (IsClosedImmersion (pullback.mapDesc A.targetProjection B.projection g))

@[reassoc (attr := simp)]
theorem supportProductInclusion_fst :
    A.supportProductInclusion B ≫
      pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) =
        pullback.fst (A.targetProjection ≫ g) (B.projection ≫ g) ≫ A.inclusion :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem supportProductInclusion_snd :
    A.supportProductInclusion B ≫
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) =
        pullback.snd (A.targetProjection ≫ g) (B.projection ≫ g) ≫ B.inclusion :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem incidenceToSupportProduct_fst :
    A.incidenceToSupportProduct B ≫
      pullback.fst (A.targetProjection ≫ g) (B.projection ≫ g) = A.incidenceFst B := by
  simp only [incidenceToSupportProduct, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem incidenceToSupportProduct_snd :
    A.incidenceToSupportProduct B ≫
      pullback.snd (A.targetProjection ≫ g) (B.projection ≫ g) = A.incidenceSnd B := by
  simp only [incidenceToSupportProduct, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- The two actual embeddings of incidence give the same ambient morphism. -/
@[reassoc]
theorem incidence_ambient_comm :
    A.incidenceInclusion B ≫ correspondenceTripleInclusion f g h =
      A.incidenceToSupportProduct B ≫ A.supportProductInclusion B := by
  apply pullback.hom_ext <;> simp

end FiniteCorrespondenceGenerator

end Motivic
