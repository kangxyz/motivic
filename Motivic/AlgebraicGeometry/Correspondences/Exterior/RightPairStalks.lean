/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.PairStalks
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Right.DiagonalAmbient

/-!
# The original right pair in the actual exterior stalks

The projections below forget the first support or the first adjacent ambient
factor, without reversing any correspondence. Their Cartesian squares exhibit
flatness as exterior base change. In particular, flatness of the first support
over the field is sufficient; flatness over its target is never asserted.
The original G,H regular diagonal list and actual coefficient stalk maps then
give the supported Tor length formula with the genuine closed-fiber quotient.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- Forget the original X,Y adjacent factor of the six-factor ambient. -/
def correspondenceSixfoldRightPairProjection : correspondenceSixfoldAmbient f g h i ⟶
    correspondenceIntersectionAmbient g h i :=
  pullback.lift
    (pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))
    (pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h))
    (by simpa only [correspondenceAmbientTarget, Category.assoc] using
      (pullback.condition (f := correspondenceAmbientTarget f g h ≫ h)
        (g := pullback.fst h i ≫ h)))

/-- The original Y,Z adjacent-product coordinate is unchanged. -/
@[reassoc (attr := simp)] theorem correspondenceSixfoldRightPairProjection_fst :
    correspondenceSixfoldRightPairProjection f g h i ≫
      pullback.fst (pullback.snd g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) :=
  pullback.lift_fst _ _ _

/-- The original Z,W adjacent-product coordinate is unchanged. -/
@[reassoc (attr := simp)] theorem correspondenceSixfoldRightPairProjection_snd :
    correspondenceSixfoldRightPairProjection f g h i ≫
      pullback.snd (pullback.snd g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) :=
  pullback.lift_snd _ _ _

/-- The right ambient projection is an actual exterior base change of the
first adjacent product's structure map. -/
theorem correspondenceSixfoldRightPairProjection_isPullback :
    IsPullback (correspondenceSixfoldRightPairProjection f g h i)
      (pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
        pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))
      (pullback.fst (pullback.snd g h ≫ h) (pullback.fst h i ≫ h) ≫
        pullback.fst g h ≫ g) (pullback.snd f g ≫ g) := by
  have hs : IsPullback (correspondenceSixfoldRightPairProjection f g h i)
      (pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h))
      (pullback.fst (pullback.snd g h ≫ h) (pullback.fst h i ≫ h))
      (pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)) := by
    refine IsPullback.of_right
      (t := (IsPullback.of_hasPullback (pullback.snd g h ≫ h)
        (pullback.fst h i ≫ h)).flip) ?_
      (correspondenceSixfoldRightPairProjection_fst f g h i)
    simpa only [correspondenceSixfoldRightPairProjection_snd,
      correspondenceAmbientTarget, Category.assoc] using
      (IsPullback.of_hasPullback (correspondenceAmbientTarget f g h ≫ h)
        (pullback.fst h i ≫ h)).flip
  exact hs.paste_vert
    (IsPullback.of_hasPullback (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)).flip

instance [Flat f] [Flat g] : Flat (correspondenceSixfoldRightPairProjection f g h i) :=
  MorphismProperty.of_isPullback
    (correspondenceSixfoldRightPairProjection_isPullback f g h i).flip
    (inferInstanceAs (Flat (pullback.snd f g ≫ g)))

/-- Forget the first adjacent factor after imposing the actual Z diagonal. -/
def correspondenceSecondDiagonalRightPairProjection : correspondenceSecondDiagonalAmbient f g h i ⟶
    correspondenceTripleProduct g h i :=
  pullback.lift
    (pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))
    (pullback.snd (correspondenceAmbientTarget f g h) (pullback.fst h i))
    (by simpa only [correspondenceAmbientTarget, Category.assoc] using
      (pullback.condition (f := correspondenceAmbientTarget f g h) (g := pullback.fst h i)))

/-- The right diagonal projection retains the original Y,Z coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSecondDiagonalRightPairProjection_fst :
    correspondenceSecondDiagonalRightPairProjection f g h i ≫
      pullback.fst (pullback.snd g h) (pullback.fst h i) =
    pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) :=
  pullback.lift_fst _ _ _

/-- The right diagonal projection retains the original Z,W coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceSecondDiagonalRightPairProjection_snd :
    correspondenceSecondDiagonalRightPairProjection f g h i ≫
      pullback.snd (pullback.snd g h) (pullback.fst h i) =
    pullback.snd (correspondenceAmbientTarget f g h) (pullback.fst h i) :=
  pullback.lift_snd _ _ _

/-- The original right diagonal and both actual projections commute. -/
@[reassoc] theorem correspondenceSecondDiagonalRightPairProjection_square :
    correspondenceSecondDiagonalRightPairProjection f g h i ≫
      correspondenceTripleInclusion g h i =
    correspondenceSecondAmbientInclusion f g h i ≫
      correspondenceSixfoldRightPairProjection f g h i := by
  apply pullback.hom_ext <;> simp

/-- Both routes give the same original pair of Z coordinates. -/
@[reassoc (attr := simp)] theorem correspondenceSixfoldRightPairProjection_middle :
    correspondenceSixfoldRightPairProjection f g h i ≫ correspondenceMiddlePair g h i =
      correspondenceSixfoldSecondMiddlePair f g h i := by
  apply pullback.hom_ext <;>
    simp [correspondenceSixfoldSecondMiddlePair, pullback.map, correspondenceAmbientTarget]

/-- The original Z coordinate is unchanged on the second diagonal. -/
@[reassoc (attr := simp)] theorem correspondenceSecondDiagonalRightPairProjection_middle :
    correspondenceSecondDiagonalRightPairProjection f g h i ≫
      correspondenceTripleMiddle g h i =
    pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
      correspondenceAmbientTarget f g h := by
  simp [correspondenceTripleMiddle, correspondenceAmbientTarget]

/-- The right-first diagonal is the exterior pullback of the original G,H
diagonal, with no reassigned or reversed support. -/
theorem correspondenceSecondDiagonal_pair_isPullback :
    IsPullback (correspondenceSecondDiagonalRightPairProjection f g h i)
      (correspondenceSecondAmbientInclusion f g h i)
      (correspondenceTripleInclusion g h i)
      (correspondenceSixfoldRightPairProjection f g h i) := by
  refine IsPullback.of_right (t := correspondenceTriple_isPullback g h i) ?_
    (correspondenceSecondDiagonalRightPairProjection_square f g h i)
  simpa only [correspondenceSecondDiagonalRightPairProjection_middle,
    correspondenceSixfoldRightPairProjection_middle] using
    correspondenceSixfoldSecondDiagonal_isPullback f g h i

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {f g h i}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual right exterior projection keeps the whole original G,H incidence. -/
abbrev rightExteriorPairProjection : F.rightIntermediateSupportProduct G H ⟶ G.incidence H :=
  pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g)

/-- The actual right coefficient projection forgets only the first support. -/
def rightExteriorCoefficientProjection : F.tripleSupportProduct G H ⟶ G.supportProduct H :=
  pullback.lift
    (pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) ≫
      pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g))
    (pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h))
    (by simpa only [supportProductTarget, Category.assoc] using
      (pullback.condition (f := F.supportProductTarget G ≫ h) (g := H.projection ≫ h)))

/-- The actual middle-support coordinate is retained. -/
@[reassoc (attr := simp)] theorem rightExteriorCoefficientProjection_fst :
    F.rightExteriorCoefficientProjection G H ≫
      pullback.fst (G.targetProjection ≫ h) (H.projection ≫ h) =
    pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) ≫
      pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) :=
  pullback.lift_fst _ _ _

/-- The actual final-support coordinate is retained. -/
@[reassoc (attr := simp)] theorem rightExteriorCoefficientProjection_snd :
    F.rightExteriorCoefficientProjection G H ≫
      pullback.snd (G.targetProjection ≫ h) (H.projection ≫ h) =
    pullback.snd (F.supportProductTarget G ≫ h) (H.projection ≫ h) :=
  pullback.lift_snd _ _ _

/-- Flatness uses precisely the first support's structure map to S, by this
actual Cartesian square. No flatness of F over Y is needed. -/
theorem rightExteriorCoefficientProjection_isPullback :
    IsPullback (F.rightExteriorCoefficientProjection G H)
      (pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h) ≫
        pullback.fst (F.targetProjection ≫ g) (G.projection ≫ g))
      (pullback.fst (G.targetProjection ≫ h) (H.projection ≫ h) ≫ G.projection ≫ g)
      (F.targetProjection ≫ g) := by
  have hs : IsPullback (F.rightExteriorCoefficientProjection G H)
      (pullback.fst (F.supportProductTarget G ≫ h) (H.projection ≫ h))
      (pullback.fst (G.targetProjection ≫ h) (H.projection ≫ h))
      (pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g)) := by
    refine IsPullback.of_right
      (t := (IsPullback.of_hasPullback (G.targetProjection ≫ h) (H.projection ≫ h)).flip)
      ?_ (F.rightExteriorCoefficientProjection_fst G H)
    simpa only [rightExteriorCoefficientProjection_snd, supportProductTarget, Category.assoc] using
      (IsPullback.of_hasPullback (F.supportProductTarget G ≫ h) (H.projection ≫ h)).flip
  exact hs.paste_vert
    (IsPullback.of_hasPullback (F.targetProjection ≫ g) (G.projection ≫ g)).flip

instance [Flat (F.targetProjection ≫ g)] : Flat (F.rightExteriorCoefficientProjection G H) :=
  MorphismProperty.of_isPullback (F.rightExteriorCoefficientProjection_isPullback G H).flip
    (inferInstanceAs (Flat (F.targetProjection ≫ g)))

/-- Both coefficient-support routes give the original right ambient projection. -/
@[reassoc] theorem rightExteriorCoefficientProjection_inclusion :
    F.rightExteriorCoefficientProjection G H ≫ G.supportProductInclusion H =
      F.tripleSupportProductInclusion G H ≫ correspondenceSixfoldRightPairProjection f g h i := by
  apply pullback.hom_ext <;> simp

/-- The actual right-first support projection retains the original pair inclusion. -/
@[reassoc (attr := simp)] theorem rightIntermediateSupportInclusion_rightPair :
    F.rightIntermediateSupportInclusion G H ≫
      correspondenceSecondDiagonalRightPairProjection f g h i =
      F.rightExteriorPairProjection G H ≫ G.incidenceInclusion H := by
  apply pullback.hom_ext <;> simp [rightIntermediateSupportInclusion, rightExteriorPairProjection]

/-- The actual exterior coefficient projection retains the original pair support map. -/
@[reassoc (attr := simp)] theorem rightIntermediateToTripleSupport_rightPair :
    F.rightIntermediateToTripleSupport G H ≫ F.rightExteriorCoefficientProjection G H =
      F.rightExteriorPairProjection G H ≫ G.incidenceToSupportProduct H := by
  apply pullback.hom_ext <;> simp [rightExteriorPairProjection]

/-- The incidence closed embedding and the actual exterior projections form a
Cartesian square, preserving the unreduced local closed fiber. -/
theorem rightExteriorIncidence_pair_isPullback :
    IsPullback (F.rightExteriorPairProjection G H)
      (F.rightIntermediateToTripleSupport G H) (G.incidenceToSupportProduct H)
      (F.rightExteriorCoefficientProjection G H) := by
  refine IsPullback.of_bot
    (t := F.rightExteriorCoefficientProjection_isPullback G H) ?_
    (F.rightIntermediateToTripleSupport_rightPair G H).symm
  simpa only [Category.assoc, rightIntermediateToTripleSupport_fst_fst,
    incidenceToSupportProduct_fst_assoc, incidenceSource, rightExteriorPairProjection] using
    (IsPullback.of_hasPullback (F.targetProjection ≫ g) (G.incidenceSource H ≫ g)).flip

/-- Exterior flatness sends each right first-stage generic point to a genuine
original G,H incidence generic point. -/
theorem rightExteriorPairProjection_mem_genericPoints [Flat (F.targetProjection ≫ g)]
    (w : F.rightIntermediateSupportProduct G H)
    (hw : w ∈ genericPoints (F.rightIntermediateSupportProduct G H)) :
    F.rightExteriorPairProjection G H w ∈ genericPoints (G.incidence H) :=
  mem_genericPoints_of_generalizing _ (Flat.generalizingMap _) w hw

/-- The actual right exterior incidence local closed fiber, including nilpotents. -/
abbrev rightExteriorClosedFiber (w : F.rightIntermediateSupportProduct G H) :=
  _root_.ChainComplex.Koszul.coefficientClosedFiber ((F.rightExteriorPairProjection G H).stalkMap
      w).hom

variable [IsSeparated h]

/-- Every actual right supported Tor degree has its original G,H pair length
multiplied by the genuine exterior closed-fiber length. -/
theorem rightExteriorSupportedTor_length [Flat f] [Flat g] [Smooth h] [Flat i]
    [Flat (F.targetProjection ≫ g)] (w : F.rightIntermediateSupportProduct G H) (n : ℕ) :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w)
        (Intersection.closedIntersectionSupportedStalkTor
          (correspondenceSecondAmbientInclusion f g h i) (F.tripleSupportProductInclusion G H)
          (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
          (F.rightIntermediate_ambient_isPullback G H) w n) =
      Module.length (G.incidenceAmbientStalk H (F.rightExteriorPairProjection G H w))
        (G.incidenceTor H (F.rightExteriorPairProjection G H w) n) *
          Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w)
            (F.rightExteriorClosedFiber G H w) := by
  let d := correspondenceTripleInclusion g h i
  let j := G.supportProductInclusion H
  let d' := correspondenceSecondAmbientInclusion f g h i
  let j' := F.tripleSupportProductInclusion G H
  let a := G.incidenceInclusion H
  let b := G.incidenceToSupportProduct H
  let a' := F.rightIntermediateSupportInclusion G H
  let b' := F.rightIntermediateToTripleSupport G H
  let uD := correspondenceSecondDiagonalRightPairProjection f g h i
  let uT := F.rightExteriorCoefficientProjection G H
  let uP := correspondenceSixfoldRightPairProjection f g h i
  let z := F.rightExteriorPairProjection G H w
  have hd : a z = uD (a' w) :=
    (congrArg (fun m => m w) (F.rightIntermediateSupportInclusion_rightPair G H)).symm
  have ht : b z = uT (b' w) :=
    (congrArg (fun m => m w) (F.rightIntermediateToTripleSupport_rightPair G H)).symm
  have he := Intersection.exteriorPairStalkTor_length
    d (a z) j (b z) (Intersection.point_eq a b d j (G.incidence_ambient_isPullback H) z)
    d' (a' w) j' (b' w)
      (Intersection.point_eq a' b' d' j' (F.rightIntermediate_ambient_isPullback G H) w)
    uD uT uP (correspondenceSecondDiagonal_pair_isPullback f g h i)
      (F.rightExteriorCoefficientProjection_inclusion G H) hd ht
      (exists_regular_kernel_correspondenceTripleInclusion g h i (a z)) n
  have hlen := (Intersection.closedIntersectionSupportedStalkTorRestrictIso
    d' j' a' b' (F.rightIntermediate_ambient_isPullback G H) w n).toLinearEquiv.length_eq
  rw [_root_.ModuleCat.length_restrictScalars_of_surjective _
    (Intersection.intersectionStalkMap_surjective a' b' d' j'
      (F.rightIntermediate_ambient_isPullback G H) w)] at hlen
  refine hlen.trans (he.trans ?_)
  congr 1
  exact Intersection.exteriorClosedFiber_length
    (F.rightExteriorPairProjection G H) b' b uT (F.rightExteriorIncidence_pair_isPullback G H) w

end FiniteCorrespondenceGenerator

end Motivic
