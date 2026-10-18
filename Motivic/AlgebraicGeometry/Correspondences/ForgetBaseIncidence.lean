/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ForgetBaseSupport
public import Motivic.AlgebraicGeometry.Correspondences.IntersectionAmbient

/-! # Original incidence geometry under forgetting an unramified base -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S T X Y Z : Scheme.{u}} (r : T ⟶ S)
  (f : X ⟶ T) (g : Y ⟶ T) (h : Z ⟶ T)

/-- Forget the base on the two adjacent products, keeping the common middle object. -/
def forgetBaseTripleMap : correspondenceTripleProduct f g h ⟶
    correspondenceTripleProduct (f ≫ r) (g ≫ r) (h ≫ r) :=
  pullback.map _ _ _ _ (forgetBaseProductMap r f g) (forgetBaseProductMap r g h)
    (𝟙 Y) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem forgetBaseTripleMap_fst :
    forgetBaseTripleMap r f g h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ forgetBaseProductMap r f g := by
  simp [forgetBaseTripleMap]

@[reassoc (attr := simp)]
theorem forgetBaseTripleMap_snd :
    forgetBaseTripleMap r f g h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ forgetBaseProductMap r g h := by
  simp [forgetBaseTripleMap]

/-- The second part of the four-factor ambient map, after forgetting its outer base. -/
def forgetBaseAmbientFactorsMap :
    pullback ((pullback.snd f g ≫ g) ≫ r) ((pullback.fst g h ≫ g) ≫ r) ⟶
      correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r) :=
  pullback.map _ _ _ _ (forgetBaseProductMap r f g) (forgetBaseProductMap r g h)
    (𝟙 S) (by simp) (by simp)

/-- The actual four-factor ambient comparison. -/
def forgetBaseAmbientMap : correspondenceIntersectionAmbient f g h ⟶
    correspondenceIntersectionAmbient (f ≫ r) (g ≫ r) (h ≫ r) :=
  forgetBaseProductMap r (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫
    forgetBaseAmbientFactorsMap r f g h

@[reassoc (attr := simp)]
theorem forgetBaseAmbientMap_fst :
    forgetBaseAmbientMap r f g h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ forgetBaseProductMap r f g := by
  simp [forgetBaseAmbientMap, forgetBaseAmbientFactorsMap]

@[reassoc (attr := simp)]
theorem forgetBaseAmbientMap_snd :
    forgetBaseAmbientMap r f g h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ forgetBaseProductMap r g h := by
  simp [forgetBaseAmbientMap, forgetBaseAmbientFactorsMap]

/-- The literal diagonal intersection square commutes. -/
theorem forgetBaseTripleInclusion_square :
    forgetBaseTripleMap r f g h ≫ correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r) =
      correspondenceTripleInclusion f g h ≫ forgetBaseAmbientMap r f g h := by
  apply pullback.hom_ext <;> simp

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseTripleMap r f g h) := by
  unfold forgetBaseTripleMap
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r f g)))
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r g h))) (by simp) (by simp)

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseAmbientFactorsMap r f g h) := by
  unfold forgetBaseAmbientFactorsMap
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r f g)))
    (inferInstanceAs (IsOpenImmersion (forgetBaseProductMap r g h))) (by simp) (by simp)

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseAmbientMap r f g h) := by
  unfold forgetBaseAmbientMap
  infer_instance

namespace FiniteCorrespondenceGenerator

variable {f g h} [IsSeparated r] [LocallyOfFiniteType r]
  [IsSeparated g] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h]
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The entire incidence is unchanged, including nilpotents and every component. -/
def forgetBaseIncidenceMap : A.incidence B ⟶ (A.forgetBase r).incidence (B.forgetBase r) :=
  pullback.map _ _ _ _ (A.forgetBaseSupportIso r).hom (B.forgetBaseSupportIso r).hom
    (𝟙 Y) (by simp) (by simp)

instance : IsIso (A.forgetBaseIncidenceMap r B) := by
  unfold forgetBaseIncidenceMap
  infer_instance

/-- The canonical incidence comparison, not a componentwise replacement. -/
def forgetBaseIncidenceIso : A.incidence B ≅ (A.forgetBase r).incidence (B.forgetBase r) :=
  asIso (A.forgetBaseIncidenceMap r B)

@[reassoc (attr := simp)]
theorem forgetBaseIncidenceMap_fst :
    A.forgetBaseIncidenceMap r B ≫ (A.forgetBase r).incidenceFst (B.forgetBase r) =
      A.incidenceFst B ≫ (A.forgetBaseSupportIso r).hom := by
  simp [forgetBaseIncidenceMap, incidenceFst]

@[reassoc (attr := simp)]
theorem forgetBaseIncidenceMap_snd :
    A.forgetBaseIncidenceMap r B ≫ (A.forgetBase r).incidenceSnd (B.forgetBase r) =
      A.incidenceSnd B ≫ (B.forgetBaseSupportIso r).hom := by
  simp [forgetBaseIncidenceMap, incidenceSnd]

/-- The final source-target projection is the original one followed by base forgetting. -/
@[reassoc]
theorem forgetBaseIncidenceMap_map :
    A.forgetBaseIncidenceMap r B ≫ (A.forgetBase r).incidenceMap (B.forgetBase r) =
      A.incidenceMap B ≫ forgetBaseProductMap r f h := by
  apply pullback.hom_ext <;>
    simp [incidenceSource, incidenceTarget]

/-- The support-product map first forgets the base and then uses the support isomorphisms. -/
def forgetBaseSupportProductFactorsMap :
    pullback ((A.targetProjection ≫ g) ≫ r) ((B.projection ≫ g) ≫ r) ⟶
      (A.forgetBase r).supportProduct (B.forgetBase r) :=
  pullback.map _ _ _ _ (A.forgetBaseSupportIso r).hom (B.forgetBaseSupportIso r).hom
    (𝟙 S) (by simp) (by simp)

instance : IsIso (A.forgetBaseSupportProductFactorsMap r B) := by
  unfold forgetBaseSupportProductFactorsMap
  infer_instance

/-- The original coefficient scheme is an open neighborhood in the forgotten coefficient scheme. -/
def forgetBaseSupportProductMap : A.supportProduct B ⟶
    (A.forgetBase r).supportProduct (B.forgetBase r) :=
  forgetBaseProductMap r (A.targetProjection ≫ g) (B.projection ≫ g) ≫
    A.forgetBaseSupportProductFactorsMap r B

instance [FormallyUnramified r] : IsOpenImmersion (A.forgetBaseSupportProductMap r B) := by
  unfold forgetBaseSupportProductMap
  infer_instance

@[reassoc (attr := simp)]
theorem forgetBaseSupportProductMap_fst :
    A.forgetBaseSupportProductMap r B ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (A.forgetBaseSupportIso r).hom := by
  simp [forgetBaseSupportProductMap, forgetBaseSupportProductFactorsMap]

@[reassoc (attr := simp)]
theorem forgetBaseSupportProductMap_snd :
    A.forgetBaseSupportProductMap r B ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (B.forgetBaseSupportIso r).hom := by
  simp [forgetBaseSupportProductMap, forgetBaseSupportProductFactorsMap]

/-- The coefficient closed immersion commutes with the original ambient comparison. -/
theorem forgetBaseSupportProduct_square :
    A.forgetBaseSupportProductMap r B ≫
        (A.forgetBase r).supportProductInclusion (B.forgetBase r) =
      A.supportProductInclusion B ≫ forgetBaseAmbientMap r f g h := by
  apply pullback.hom_ext <;> simp

/-- The original incidence point in the coefficient scheme has the expected image. -/
@[reassoc]
theorem forgetBaseIncidenceMap_supportProduct :
    A.forgetBaseIncidenceMap r B ≫
        (A.forgetBase r).incidenceToSupportProduct (B.forgetBase r) =
      A.incidenceToSupportProduct B ≫ A.forgetBaseSupportProductMap r B := by
  apply pullback.hom_ext <;> simp

/-- The original incidence point in the triple scheme has the expected image. -/
@[reassoc]
theorem forgetBaseIncidenceMap_inclusion :
    A.forgetBaseIncidenceMap r B ≫ (A.forgetBase r).incidenceInclusion (B.forgetBase r) =
      A.incidenceInclusion B ≫ forgetBaseTripleMap r f g h := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, incidenceInclusion_fst, incidenceInclusion_snd,
      incidenceInclusion_fst_assoc, incidenceInclusion_snd_assoc,
      forgetBaseIncidenceMap_fst_assoc, forgetBaseIncidenceMap_snd_assoc,
      forgetBaseSupportIso_hom_inclusion, forgetBaseTripleMap_fst,
      forgetBaseTripleMap_snd]

end FiniteCorrespondenceGenerator

end Motivic
