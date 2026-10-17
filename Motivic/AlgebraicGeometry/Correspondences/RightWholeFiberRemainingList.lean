/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightImageIncidenceFiber
public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardKoszul

/-!
# One original remaining-Y list on the entire right finite fiber

A single smooth Y-diagonal list is chosen at the middle point of a fixed
image-side point. Every original point of its entire source fiber uses the
same list, transported only by the actual equality of middle points. The
literal finite-map stalk action agrees with the original ambient action.
The image of an actual triple-incidence point supplies the diagonal-range
witness geometrically. No source-point list is chosen independently.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (y : F.rightIntermediateImageProduct G H)

/-- Every point in the original full fiber has the fixed image-side middle point. -/
theorem rightFiberMiddlePoint (x : {w : F.rightIntermediateSupportProduct G H //
    F.rightIntermediateImageMap G H w = y}) :
    F.rightImageMiddlePair G H y = F.rightSupportMiddlePair G H x.1 := by
  exact (congrArg (F.rightImageMiddlePair G H) x.2.symm).trans
    (congrArg (fun m => m x.1) (F.rightIntermediateImageMap_middlePair G H))

/-- The only change in the middle stalk is its proved equality of original points. -/
def rightFiberMiddleStalkIso (x : {w : F.rightIntermediateSupportProduct G H //
    F.rightIntermediateImageMap G H w = y}) :
    (pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y) ≅
      (pullback g g).presheaf.stalk (F.rightSupportMiddlePair G H x.1) :=
  (pullback g g).presheaf.stalkCongr (.of_eq (F.rightFiberMiddlePoint G H y x))

/-- The same fixed middle list at every original source-fiber point. -/
def rightFiberMiddleList
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = y}) :
    List ((pullback g g).presheaf.stalk (F.rightSupportMiddlePair G H x.1)) :=
  s.map (F.rightFiberMiddleStalkIso G H y x).hom.hom

/-- The genuine common remaining list in the original image-side structure stalk. -/
def rightTargetRemainingList
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y))) :
    List ((F.rightIntermediateImageProduct G H).presheaf.stalk y) :=
  s.map ((F.rightImageMiddlePair G H).stalkMap y).hom

/-- The fixed target list acts on every original source through the literal
finite morphism and the actual equality identifying its image point. -/
@[reassoc] theorem rightFiberRemainingStalkMap
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = y}) :
    (F.rightImageMiddlePair G H).stalkMap y ≫
        Graph.alignedStalkMap (F.rightIntermediateImageMap G H) x.1 y x.2.symm =
      (F.rightFiberMiddleStalkIso G H y x).hom ≫
        (F.rightSupportMiddlePair G H).stalkMap x.1 := by
  rcases x with ⟨w, hw⟩
  subst y
  simp only [Graph.alignedStalkMap_rfl, rightFiberMiddleStalkIso,
    ← Scheme.Hom.stalkMap_comp]
  exact Scheme.Hom.stalkMap_congr_hom _ _ (F.rightIntermediateImageMap_middlePair G H) w

/-- One target list gives the actual support-middle image list simultaneously
at every original point of the full fiber. -/
theorem rightFiberRemainingList_map
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = y}) :
    (F.rightTargetRemainingList G H y s).map
        (Graph.alignedStalkMap (F.rightIntermediateImageMap G H) x.1 y x.2.symm).hom =
      (F.rightFiberMiddleList G H y s x).map
        ((F.rightSupportMiddlePair G H).stalkMap x.1).hom := by
  simp only [rightTargetRemainingList, rightFiberMiddleList, List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.rightFiberRemainingStalkMap G H y x) a

/-- The literal original ambient and finite-image routes carry the same fixed
list across the whole fiber, without any independently assumed source list. -/
theorem rightFiberRemainingList_square
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = y}) :
    (F.rightTargetRemainingList G H y s).map
        (Graph.alignedStalkMap (F.rightIntermediateImageMap G H) x.1 y x.2.symm).hom =
      ((F.rightFiberMiddleList G H y s x).map
        (F.rightAmbientMiddleStalkMap G H x.1).hom).map
          ((F.rightIntermediateAmbientInclusion G H).stalkMap x.1).hom :=
  (F.rightFiberRemainingList_map G H y s x).trans
    (F.rightAmbientMiddleList_map G H x.1 (F.rightFiberMiddleList G H y s x)).symm

private theorem stalkCongr_ideal {Q : Scheme.{u}} (J : Q.IdealSheafData)
    {z z' : Q} (e : z = z') (s : List (Q.presheaf.stalk z))
    (hs : J.stalk z = Ideal.ofList s) :
    J.stalk z' = Ideal.ofList (s.map (Q.presheaf.stalkCongr (.of_eq e)).hom.hom) := by
  subst z'
  simpa using hs

/-- The transported list still generates the very same original diagonal ideal,
now at each source point's equal middle point. -/
theorem rightFiberMiddleList_kernel
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)))
    (hs : (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H y) = Ideal.ofList s)
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = y}) :
    (pullback.diagonal g).ker.stalk (F.rightSupportMiddlePair G H x.1) =
      Ideal.ofList (F.rightFiberMiddleList G H y s x) :=
  stalkCongr_ideal (pullback.diagonal g).ker (F.rightFiberMiddlePoint G H y x) s hs

/-- Smoothness chooses one regular middle list at the fixed image-side point;
its length is local and no common smooth dimension is imposed. -/
theorem exists_rightTargetRemainingList [Smooth g] [IsSeparated g]
    (hy : ∃ z : Y, pullback.diagonal g z = F.rightImageMiddlePair G H y) :
    ∃ s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)),
      RingTheory.Sequence.IsRegular
        ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)) s ∧
      (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H y) = Ideal.ofList s := by
  obtain ⟨z, hz⟩ := hy
  have hex : ∃ s : List ((pullback g g).presheaf.stalk (pullback.diagonal g z)),
      RingTheory.Sequence.IsRegular
        ((pullback g g).presheaf.stalk (pullback.diagonal g z)) s ∧
      (pullback.diagonal g).ker.stalk (pullback.diagonal g z) = Ideal.ofList s := by
    obtain ⟨s, hs, hker⟩ := Diagonal.exists_regular_kernel_of_smooth g z
    exact ⟨s, hs, ((pullback.diagonal g).ker_stalk z).trans hker⟩
  exact (congrArg (fun q : (pullback g g : Scheme.{u}) =>
    ∃ s : List ((pullback g g).presheaf.stalk q),
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk q) s ∧
        (pullback.diagonal g).ker.stalk q = Ideal.ofList s) hz).mp hex

omit y in
/-- An actual triple-incidence image lies over the actual remaining diagonal,
so the final geometric application supplies its own range witness. -/
theorem rightTripleImageMiddle_mem_diagonal (w : F.tripleIncidence G H) :
    ∃ z : Y, pullback.diagonal g z = F.rightImageMiddlePair G H
      (F.rightIntermediateImageMap G H (F.tripleIncidenceToRightSupportProduct G H w)) := by
  refine ⟨F.targetProjection (F.incidenceFst G (F.tripleIncidenceFst G H w)), ?_⟩
  have he := (F.rightRemainingDiagonal_isPullback G H).w
  exact (congrArg (fun m => m w) he).trans
    (congrArg (fun m => m (F.tripleIncidenceToRightSupportProduct G H w))
      (F.rightIntermediateImageMap_middlePair G H)).symm

omit y in
/-- At every actual triple image, smoothness constructs a single original
remaining list for the complete finite source fiber. -/
theorem exists_rightTripleImageRemainingList [Smooth g] [IsSeparated g]
    (w : F.tripleIncidence G H) :
    let y := F.rightIntermediateImageMap G H (F.tripleIncidenceToRightSupportProduct G H w)
    ∃ s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)),
      RingTheory.Sequence.IsRegular
        ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H y)) s ∧
      (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H y) = Ideal.ofList s :=
  F.exists_rightTargetRemainingList G H _ (F.rightTripleImageMiddle_mem_diagonal G H w)

omit y in
/-- The all-fiber list square is exactly the original finite-affine Euler API,
including its original target point and source-stalk map. -/
theorem rightOriginalFiberRemainingList_map
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) :
    (F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
        (FiniteSchemeEuler.originalFiberStalkMap (F.rightIntermediateImageMap G H) V.2 p x).hom =
      (F.rightFiberMiddleList G H (V.2.fromSpec p) s x).map
        ((F.rightSupportMiddlePair G H).stalkMap x.1).hom :=
  F.rightFiberRemainingList_map G H (V.2.fromSpec p) s x

end Motivic.FiniteCorrespondenceGenerator
