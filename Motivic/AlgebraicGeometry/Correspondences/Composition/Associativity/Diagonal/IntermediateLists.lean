/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.SecondMiddlePair

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalIdeals
public import Motivic.Aglib.AlgebraicGeometry.Graph.CommonStalkTransport

/-!
# The actual remaining-diagonal list through the finite image product

The remaining Z-diagonal map on the genuine first-stage support agrees both
with the original six-factor map and with the map from its finite intermediate
image product. Their literal pointed stalk squares therefore transport one
and the same original middle list. No independently chosen list, finite
individual source-stalk algebra, or descended ambient complex is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable {f g h i}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual remaining middle pair on the first-stage support I_FG times H. -/
def leftSupportMiddlePair : F.leftIntermediateSupportProduct G H ⟶ pullback h h :=
  pullback.map _ _ h h (F.incidenceTarget G) H.projection (𝟙 S) (by simp) (by simp)

/-- The actual remaining middle pair on the whole intermediate-image product. -/
def leftImageMiddlePair : F.leftIntermediateImageProduct G H ⟶ pullback h h :=
  pullback.map _ _ h h ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection
    (𝟙 S) (by simp) (by simp)

/-- The first-stage middle pair retains its second, third-support projection. -/
@[reassoc (attr := simp)] theorem leftSupportMiddlePair_snd :
    F.leftSupportMiddlePair G H ≫ pullback.snd h h =
      pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫ H.projection :=
  pullback.lift_snd _ _ _

/-- The finite image-product map preserves the same actual remaining middle pair. -/
@[reassoc] theorem leftIntermediateImageMap_middlePair :
    F.leftIntermediateImageMap G H ≫ F.leftImageMiddlePair G H =
      F.leftSupportMiddlePair G H := by
  apply pullback.hom_ext <;>
    simp [leftImageMiddlePair, leftSupportMiddlePair, pullback.map, Category.assoc,
      pullback.lift_fst, pullback.lift_snd]

/-- The original six-factor remaining pair restricts to that same first-stage pair. -/
@[reassoc] theorem leftIntermediateAmbientInclusion_middlePair :
    F.leftIntermediateAmbientInclusion G H ≫
      correspondenceSixfoldSecondMiddlePair f g h i = F.leftSupportMiddlePair G H := by
  apply pullback.hom_ext
  · simp [leftIntermediateAmbientInclusion, leftSupportMiddlePair, pullback.map,
      correspondenceAmbientTarget, correspondenceTripleTarget, incidenceTarget,
      pullback.lift_fst, targetProjection]
  · simp only [Category.assoc, correspondenceSixfoldSecondMiddlePair_snd,
      leftIntermediateAmbientInclusion, Category.assoc,
      correspondenceFirstDiagonalInclusion_snd_assoc,
      leftIntermediateSupportInclusion_snd_assoc, leftSupportMiddlePair_snd]
    rfl

/-- The first-stage ambient embedding recovers the actual full triple embedding. -/
@[reassoc] theorem tripleToLeftSupport_ambient :
    F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateAmbientInclusion G H =
      F.tripleIncidenceSixfoldInclusion G H := by
  rw [leftIntermediateAmbientInclusion, ← Category.assoc,
    ← F.tripleIncidence_firstDiagonal_comm G H]
  rfl

/-- At an actual triple point, both constructions use the exact same remaining
middle self-product point. -/
theorem tripleRemainingMiddlePoint (w : F.tripleIncidence G H) :
    F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w) =
      correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w) := by
  have he : F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftSupportMiddlePair G H =
      F.tripleIncidenceSixfoldInclusion G H ≫
        correspondenceSixfoldSecondMiddlePair f g h i := by
    rw [← F.leftIntermediateAmbientInclusion_middlePair G H,
      ← Category.assoc, F.tripleToLeftSupport_ambient G H]
  exact congrArg (fun m => m w) he

/-- Canonical point transport of the original common Z-diagonal stalk. -/
def tripleRemainingMiddleStalkIso (w : F.tripleIncidence G H) :
    (pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)) ≅
      (pullback h h).presheaf.stalk
        (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w)) :=
  (pullback h h).presheaf.stalkCongr (.of_eq (F.tripleRemainingMiddlePoint G H w).symm)

/-- The pointed map from the original middle stalk to the actual image-product stalk. -/
def leftImageMiddleStalkMap (w : F.leftIntermediateSupportProduct G H) :
    (pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H w) ⟶
      (F.leftIntermediateImageProduct G H).presheaf.stalk (F.leftIntermediateImageMap G H w) :=
  Graph.alignedStalkMap (F.leftImageMiddlePair G H) (F.leftIntermediateImageMap G H w)
    (F.leftSupportMiddlePair G H w)
    (congrArg (fun m => m w) (F.leftIntermediateImageMap_middlePair G H)).symm

/-- The pointed map from that same middle stalk to the original six-factor ambient stalk. -/
def leftAmbientMiddleStalkMap (w : F.leftIntermediateSupportProduct G H) :
    (pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H w) ⟶
      (correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (F.leftIntermediateAmbientInclusion G H w) :=
  Graph.alignedStalkMap (correspondenceSixfoldSecondMiddlePair f g h i)
    (F.leftIntermediateAmbientInclusion G H w) (F.leftSupportMiddlePair G H w)
    (congrArg (fun m => m w) (F.leftIntermediateAmbientInclusion_middlePair G H)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The image-product stalk map followed by the actual finite-map stalk map
is exactly the first-stage remaining-middle stalk map. -/
@[reassoc] theorem leftImageMiddleStalkMap_comp (w : F.leftIntermediateSupportProduct G H) :
    F.leftImageMiddleStalkMap G H w ≫ (F.leftIntermediateImageMap G H).stalkMap w =
      (F.leftSupportMiddlePair G H).stalkMap w := by
  simp only [leftImageMiddleStalkMap, Graph.alignedStalkMap, Category.assoc,
    ← Scheme.Hom.stalkMap_comp]
  exact (Scheme.Hom.stalkMap_congr_hom _ _
    (F.leftIntermediateImageMap_middlePair G H).symm w).symm

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the genuine first-stage quotient preserves the same original
middle stalk map, with its actual scalar action. -/
@[reassoc] theorem leftAmbientMiddleStalkMap_comp (w : F.leftIntermediateSupportProduct G H) :
    F.leftAmbientMiddleStalkMap G H w ≫ (F.leftIntermediateAmbientInclusion G H).stalkMap w =
      (F.leftSupportMiddlePair G H).stalkMap w := by
  simp only [leftAmbientMiddleStalkMap, Graph.alignedStalkMap, Category.assoc,
    ← Scheme.Hom.stalkMap_comp]
  exact (Scheme.Hom.stalkMap_congr_hom _ _
    (F.leftIntermediateAmbientInclusion_middlePair G H).symm w).symm

/-- The remaining list on the finite image product maps to the literal first-stage list. -/
theorem leftImageMiddleList_map (w : F.leftIntermediateSupportProduct G H)
    (s : List ((pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H w))) :
    (s.map (F.leftImageMiddleStalkMap G H w).hom).map
        ((F.leftIntermediateImageMap G H).stalkMap w).hom =
      s.map ((F.leftSupportMiddlePair G H).stalkMap w).hom := by
  rw [List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.leftImageMiddleStalkMap_comp G H w) a

/-- The original ambient remaining list maps to that same literal first-stage list. -/
theorem leftAmbientMiddleList_map (w : F.leftIntermediateSupportProduct G H)
    (s : List ((pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H w))) :
    (s.map (F.leftAmbientMiddleStalkMap G H w).hom).map
        ((F.leftIntermediateAmbientInclusion G H).stalkMap w).hom =
      s.map ((F.leftSupportMiddlePair G H).stalkMap w).hom := by
  rw [List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.leftAmbientMiddleStalkMap_comp G H w) a

/-- The exact same original middle list is used by ambient replacement and
finite intermediate-image projection, after their literal stalk maps. -/
theorem leftRemainingList_square (w : F.leftIntermediateSupportProduct G H)
    (s : List ((pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H w))) :
    (s.map (F.leftImageMiddleStalkMap G H w).hom).map
        ((F.leftIntermediateImageMap G H).stalkMap w).hom =
      (s.map (F.leftAmbientMiddleStalkMap G H w).hom).map
        ((F.leftIntermediateAmbientInclusion G H).stalkMap w).hom :=
  (F.leftImageMiddleList_map G H w s).trans (F.leftAmbientMiddleList_map G H w s).symm

end FiniteCorrespondenceGenerator

end Motivic
