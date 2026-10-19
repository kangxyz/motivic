/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Right.DiagonalAmbient
public import Motivic.Aglib.AlgebraicGeometry.Graph.CommonStalkTransport

/-!
# The right-first original remaining-Y diagonal and stalk list

The literal Y self-product maps commute with the original six-factor
embedding and the finite right image-product map. The original associator
identifies full triple incidence with the remaining diagonal pullback.
Actual pointed stalk maps consequently carry the same original Y list.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual remaining Y pair on first-support times right incidence. -/
def rightSupportMiddlePair : F.rightIntermediateSupportProduct G H ⟶ pullback g g :=
  pullback.map _ _ g g F.targetProjection (G.incidenceSource H) (𝟙 S)
    (by simp) (by simp)

/-- The actual remaining Y pair on first-support times the right scheme image. -/
def rightImageMiddlePair : F.rightIntermediateImageProduct G H ⟶ pullback g g :=
  pullback.map _ _ g g F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i)
    (𝟙 S) (by simp) (by simp)

/-- The right-first middle pair keeps the original first-support Y coordinate. -/
@[reassoc (attr := simp)] theorem rightSupportMiddlePair_fst :
    F.rightSupportMiddlePair G H ≫ pullback.fst g g =
      pullback.fst (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫ F.targetProjection :=
  pullback.lift_fst _ _ _

/-- The right-first middle pair keeps the original right-incidence Y coordinate. -/
@[reassoc (attr := simp)] theorem rightSupportMiddlePair_snd :
    F.rightSupportMiddlePair G H ≫ pullback.snd g g =
      pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫ G.incidenceSource H :=
  pullback.lift_snd _ _ _

/-- The original finite image-product morphism preserves both remaining Y coordinates. -/
@[reassoc] theorem rightIntermediateImageMap_middlePair :
    F.rightIntermediateImageMap G H ≫ F.rightImageMiddlePair G H =
      F.rightSupportMiddlePair G H := by
  apply pullback.hom_ext <;>
    simp [rightImageMiddlePair, rightSupportMiddlePair, pullback.map, Category.assoc,
      pullback.lift_fst, pullback.lift_snd]

/-- The original six-factor Y pair restricts to the same literal right-first pair. -/
@[reassoc] theorem rightIntermediateAmbientInclusion_middlePair :
    F.rightIntermediateAmbientInclusion G H ≫
      correspondenceSixfoldFirstMiddlePair f g h i = F.rightSupportMiddlePair G H := by
  calc
    _ = F.rightIntermediateToTripleSupport G H ≫ F.tripleSupportProductInclusion G H ≫
        correspondenceSixfoldFirstMiddlePair f g h i := by
      rw [rightIntermediateAmbientInclusion, F.rightIntermediate_ambient_comm G H, Category.assoc]
    _ = _ := by
      apply pullback.hom_ext
      · simp only [correspondenceSixfoldFirstMiddlePair, Category.assoc,
          correspondenceMiddlePair_fst, tripleSupportProductInclusion_fst_assoc,
          supportProductInclusion_fst_assoc, rightIntermediateToTripleSupport_fst_fst_assoc,
          rightSupportMiddlePair_fst]
      · simp only [correspondenceSixfoldFirstMiddlePair, Category.assoc,
          correspondenceMiddlePair_snd, tripleSupportProductInclusion_fst_assoc,
          supportProductInclusion_snd_assoc, rightIntermediateToTripleSupport_fst_snd_assoc,
          rightSupportMiddlePair_snd]
        rfl

/-- The existing full-incidence associator retains the first support in the
right remaining-diagonal inclusion. -/
@[reassoc (attr := simp)] theorem tripleIncidenceToRightSupportProduct_fst :
    F.tripleIncidenceToRightSupportProduct G H ≫
      pullback.fst (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) =
    F.tripleIncidenceFst G H ≫ F.incidenceFst G := by
  simp only [tripleIncidenceToRightSupportProduct, pullback.mapDesc, pullback.map,
    Category.assoc, pullback.lift_fst, Category.comp_id, tripleIncidenceAssoc_fst]

/-- The two parenthesizations keep the same three original exterior-support coordinates. -/
@[reassoc] theorem tripleToRightSupport_coefficient :
    F.tripleIncidenceToRightSupportProduct G H ≫ F.rightIntermediateToTripleSupport G H =
    F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp
  · simp

/-- The right-first ambient route recovers the same original full triple embedding. -/
@[reassoc] theorem tripleToRightSupport_ambient :
    F.tripleIncidenceToRightSupportProduct G H ≫ F.rightIntermediateAmbientInclusion G H =
    F.tripleIncidenceSixfoldInclusion G H := by
  calc
    _ = (F.tripleIncidenceToRightSupportProduct G H ≫
        F.rightIntermediateToTripleSupport G H) ≫ F.tripleSupportProductInclusion G H := by
      simp only [rightIntermediateAmbientInclusion, Category.assoc,
        rightIntermediate_ambient_comm]
    _ = (F.tripleIncidenceToLeftSupportProduct G H ≫
        F.leftIntermediateToTripleSupport G H) ≫ F.tripleSupportProductInclusion G H := by
      rw [F.tripleToRightSupport_coefficient G H]
    _ = _ := by
      simpa only [tripleIncidenceSixfoldInclusion, Category.assoc] using
        (F.tripleIncidence_sixfold_isPullback G H).w.symm

/-- Full original triple incidence is the genuine remaining Y-diagonal pullback,
using its established associator and no finiteness of the right-pair projection. -/
theorem rightRemainingDiagonal_isPullback :
    IsPullback (F.tripleIncidenceFst G H ≫ F.incidenceFst G ≫ F.targetProjection)
      (F.tripleIncidenceToRightSupportProduct G H)
      (pullback.diagonal g) (F.rightSupportMiddlePair G H) :=
  (pullback_map_diagonal_isPullback F.targetProjection (G.incidenceSource H) g).of_iso
    (F.tripleIncidenceAssoc G H).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      apply (cancel_epi (F.tripleIncidenceAssoc G H).hom).mp
      simp)
    (by simp [tripleIncidenceToRightSupportProduct]) (by simp)
    (by simp [rightSupportMiddlePair])

/-- The original remaining-incidence ideal is exactly the pulled-back Y-diagonal ideal. -/
theorem rightRemainingDiagonal_kernel [IsSeparated g] :
    (F.tripleIncidenceToRightSupportProduct G H).ker =
      (pullback.diagonal g).ker.comap (F.rightSupportMiddlePair G H) :=
  ker_eq_comap_of_isPullback _ _ _ _ (F.rightRemainingDiagonal_isPullback G H).flip

/-- At an actual triple point, both constructions use the exact same remaining
middle self-product point. -/
theorem tripleRightRemainingMiddlePoint (w : F.tripleIncidence G H) :
    F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w) =
      correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w) := by
  have he : F.tripleIncidenceToRightSupportProduct G H ≫ F.rightSupportMiddlePair G H =
      F.tripleIncidenceSixfoldInclusion G H ≫
        correspondenceSixfoldFirstMiddlePair f g h i := by
    rw [← F.rightIntermediateAmbientInclusion_middlePair G H,
      ← Category.assoc, F.tripleToRightSupport_ambient G H]
  exact congrArg (fun m => m w) he

/-- Canonical point transport of the original common Y-diagonal stalk. -/
def tripleRightRemainingMiddleStalkIso (w : F.tripleIncidence G H) :
    (pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)) ≅
      (pullback g g).presheaf.stalk
        (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w)) :=
  (pullback g g).presheaf.stalkCongr (.of_eq (F.tripleRightRemainingMiddlePoint G H w).symm)

/-- The pointed map from the original middle stalk to the actual image-product stalk. -/
def rightImageMiddleStalkMap (w : F.rightIntermediateSupportProduct G H) :
    (pullback g g).presheaf.stalk (F.rightSupportMiddlePair G H w) ⟶
      (F.rightIntermediateImageProduct G H).presheaf.stalk (F.rightIntermediateImageMap G H w) :=
  Graph.alignedStalkMap (F.rightImageMiddlePair G H) (F.rightIntermediateImageMap G H w)
    (F.rightSupportMiddlePair G H w)
    (congrArg (fun m => m w) (F.rightIntermediateImageMap_middlePair G H)).symm

/-- The pointed map from that same middle stalk to the original six-factor ambient stalk. -/
def rightAmbientMiddleStalkMap (w : F.rightIntermediateSupportProduct G H) :
    (pullback g g).presheaf.stalk (F.rightSupportMiddlePair G H w) ⟶
      (correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (F.rightIntermediateAmbientInclusion G H w) :=
  Graph.alignedStalkMap (correspondenceSixfoldFirstMiddlePair f g h i)
    (F.rightIntermediateAmbientInclusion G H w) (F.rightSupportMiddlePair G H w)
    (congrArg (fun m => m w) (F.rightIntermediateAmbientInclusion_middlePair G H)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The image-product stalk map followed by the actual finite-map stalk map
is exactly the first-stage remaining-middle stalk map. -/
@[reassoc] theorem rightImageMiddleStalkMap_comp (w : F.rightIntermediateSupportProduct G H) :
    F.rightImageMiddleStalkMap G H w ≫ (F.rightIntermediateImageMap G H).stalkMap w =
      (F.rightSupportMiddlePair G H).stalkMap w := by
  simp only [rightImageMiddleStalkMap, Graph.alignedStalkMap, Category.assoc,
    ← Scheme.Hom.stalkMap_comp]
  exact (Scheme.Hom.stalkMap_congr_hom _ _
    (F.rightIntermediateImageMap_middlePair G H).symm w).symm

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the genuine first-stage quotient preserves the same original
middle stalk map, with its actual scalar action. -/
@[reassoc] theorem rightAmbientMiddleStalkMap_comp (w : F.rightIntermediateSupportProduct G H) :
    F.rightAmbientMiddleStalkMap G H w ≫ (F.rightIntermediateAmbientInclusion G H).stalkMap w =
      (F.rightSupportMiddlePair G H).stalkMap w := by
  simp only [rightAmbientMiddleStalkMap, Graph.alignedStalkMap, Category.assoc,
    ← Scheme.Hom.stalkMap_comp]
  exact (Scheme.Hom.stalkMap_congr_hom _ _
    (F.rightIntermediateAmbientInclusion_middlePair G H).symm w).symm

/-- The remaining list on the finite image product maps to the literal first-stage list. -/
theorem rightImageMiddleList_map (w : F.rightIntermediateSupportProduct G H)
    (s : List ((pullback g g).presheaf.stalk (F.rightSupportMiddlePair G H w))) :
    (s.map (F.rightImageMiddleStalkMap G H w).hom).map
        ((F.rightIntermediateImageMap G H).stalkMap w).hom =
      s.map ((F.rightSupportMiddlePair G H).stalkMap w).hom := by
  rw [List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.rightImageMiddleStalkMap_comp G H w) a

/-- The original ambient remaining list maps to that same literal first-stage list. -/
theorem rightAmbientMiddleList_map (w : F.rightIntermediateSupportProduct G H)
    (s : List ((pullback g g).presheaf.stalk (F.rightSupportMiddlePair G H w))) :
    (s.map (F.rightAmbientMiddleStalkMap G H w).hom).map
        ((F.rightIntermediateAmbientInclusion G H).stalkMap w).hom =
      s.map ((F.rightSupportMiddlePair G H).stalkMap w).hom := by
  rw [List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.rightAmbientMiddleStalkMap_comp G H w) a

/-- The exact same original middle list is used by ambient replacement and
finite intermediate-image projection, after their literal stalk maps. -/
theorem rightRemainingList_square (w : F.rightIntermediateSupportProduct G H)
    (s : List ((pullback g g).presheaf.stalk (F.rightSupportMiddlePair G H w))) :
    (s.map (F.rightImageMiddleStalkMap G H w).hom).map
        ((F.rightIntermediateImageMap G H).stalkMap w).hom =
      (s.map (F.rightAmbientMiddleStalkMap G H w).hom).map
        ((F.rightIntermediateAmbientInclusion G H).stalkMap w).hom :=
  (F.rightImageMiddleList_map G H w s).trans (F.rightAmbientMiddleList_map G H w s).symm

end Motivic.FiniteCorrespondenceGenerator
