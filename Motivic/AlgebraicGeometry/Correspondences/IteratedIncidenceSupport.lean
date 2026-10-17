/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleIncidence
public import Motivic.AlgebraicGeometry.Correspondences.IntersectionAmbient

/-!
# The actual finite intermediate-image product maps

The projection-formula domains are products with the whole pair-incidence
scheme, and the finite maps are products of its actual scheme-image factor
with an identity. In the right order this is the identity on the first support
times the second pair's finite image factor. It is not the generally nonfinite
projection from triple incidence to the second pair. All nilpotents remain.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- A finite pair-incidence map factors finitely through its actual scheme image. -/
theorem incidenceToImage_isFinite [IsSeparated h] : IsFinite (F.incidenceMap G).toImage := by
  have : IsFinite ((F.incidenceMap G).toImage ≫ (F.incidenceMap G).imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  exact IsFinite.of_comp _ (F.incidenceMap G).imageι

/-- The pair incidence times the third support, before imposing the second diagonal. -/
abbrev leftIntermediateSupportProduct : Scheme.{u} :=
  pullback (F.incidenceTarget G ≫ h) (H.projection ≫ h)

/-- The actual intermediate image times the third support. -/
abbrev leftIntermediateImageProduct : Scheme.{u} :=
  pullback ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h) (H.projection ≫ h)

/-- The first support times the second pair incidence. -/
abbrev rightIntermediateSupportProduct : Scheme.{u} :=
  pullback (F.targetProjection ≫ g) (G.incidenceSource H ≫ g)

/-- The first support times the actual image of the second pair incidence. -/
abbrev rightIntermediateImageProduct : Scheme.{u} :=
  pullback (F.targetProjection ≫ g) ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g)

/-- The left projection-formula map is the image factor times the identity. -/
def leftIntermediateImageMap : F.leftIntermediateSupportProduct G H ⟶
    F.leftIntermediateImageProduct G H :=
  pullback.map _ _ _ _ (F.incidenceMap G).toImage (𝟙 H.scheme) (𝟙 S)
    (by simp [Category.assoc]) (by simp)

/-- The right projection-formula map is the identity times the image factor. -/
def rightIntermediateImageMap : F.rightIntermediateSupportProduct G H ⟶
    F.rightIntermediateImageProduct G H :=
  pullback.map _ _ _ _ (𝟙 F.scheme) (G.incidenceMap H).toImage (𝟙 S)
    (by simp) (by simp [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/-- The actual left image-product map is finite without flatness assumptions. -/
instance [IsSeparated h] : IsFinite (F.leftIntermediateImageMap G H) := by
  let := F.incidenceToImage_isFinite G
  unfold leftIntermediateImageMap
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    (inferInstanceAs (IsFinite (F.incidenceMap G).toImage))
    (inferInstanceAs (IsFinite (𝟙 H.scheme))) (by simp [Category.assoc]) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The actual right image-product map is finite even when triple-to-right-pair is not. -/
instance [IsSeparated i] : IsFinite (F.rightIntermediateImageMap G H) := by
  let := G.incidenceToImage_isFinite H
  unfold rightIntermediateImageMap
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    (inferInstanceAs (IsFinite (𝟙 F.scheme)))
    (inferInstanceAs (IsFinite (G.incidenceMap H).toImage)) (by simp) (by simp [Category.assoc])

/-- The left finite map retains the literal pair-incidence scheme-image factor. -/
@[reassoc (attr := simp)] theorem leftIntermediateImageMap_fst :
    F.leftIntermediateImageMap G H ≫
      pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h) (H.projection ≫ h) =
    pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫ (F.incidenceMap G).toImage :=
  pullback.lift_fst _ _ _

/-- The third support is unchanged by the left finite map. -/
@[reassoc (attr := simp)] theorem leftIntermediateImageMap_snd :
    F.leftIntermediateImageMap G H ≫
      pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h) (H.projection ≫ h) =
    pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h) := by
  simp only [leftIntermediateImageMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The first support is unchanged by the right finite map. -/
@[reassoc (attr := simp)] theorem rightIntermediateImageMap_fst :
    F.rightIntermediateImageMap G H ≫
      pullback.fst (F.targetProjection ≫ g)
        ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) =
    pullback.fst (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) := by
  simp only [rightIntermediateImageMap, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The right finite map retains the literal second-pair scheme-image factor. -/
@[reassoc (attr := simp)] theorem rightIntermediateImageMap_snd :
    F.rightIntermediateImageMap G H ≫
      pullback.snd (F.targetProjection ≫ g)
        ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) =
    pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫
      (G.incidenceMap H).toImage := pullback.lift_snd _ _ _

/-- The left remaining diagonal embeds actual triple incidence into its support product. -/
abbrev tripleIncidenceToLeftSupportProduct : F.tripleIncidence G H ⟶
    F.leftIntermediateSupportProduct G H :=
  pullback.mapDesc (F.incidenceTarget G) H.projection h

instance [IsSeparated h] : IsClosedImmersion (F.tripleIncidenceToLeftSupportProduct G H) :=
  inferInstanceAs (IsClosedImmersion (pullback.mapDesc (F.incidenceTarget G) H.projection h))

/-- The right remaining diagonal uses the actual associator followed by its closed embedding. -/
def tripleIncidenceToRightSupportProduct : F.tripleIncidence G H ⟶
    F.rightIntermediateSupportProduct G H :=
  (F.tripleIncidenceAssoc G H).hom ≫ pullback.mapDesc F.targetProjection (G.incidenceSource H) g

instance [IsSeparated g] : IsClosedImmersion (F.tripleIncidenceToRightSupportProduct G H) :=
  inferInstanceAs (IsClosedImmersion ((F.tripleIncidenceAssoc G H).hom ≫
    pullback.mapDesc F.targetProjection (G.incidenceSource H) g))

/-- The left remaining-diagonal embedding remembers the actual first pair incidence. -/
@[reassoc (attr := simp)] theorem tripleIncidenceToLeftSupportProduct_fst :
    F.tripleIncidenceToLeftSupportProduct G H ≫
      pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h) =
    F.tripleIncidenceFst G H := by
  simp only [tripleIncidenceToLeftSupportProduct, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The right remaining-diagonal embedding remembers the actual second pair incidence. -/
@[reassoc (attr := simp)] theorem tripleIncidenceToRightSupportProduct_snd :
    F.tripleIncidenceToRightSupportProduct G H ≫
      pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) =
    F.tripleIncidenceToRightPair G H := by
  simp only [tripleIncidenceToRightSupportProduct, pullback.mapDesc, pullback.map,
    Category.assoc, pullback.lift_snd, Category.comp_id, tripleIncidenceAssoc_snd]

end Motivic.FiniteCorrespondenceGenerator
