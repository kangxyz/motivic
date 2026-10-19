/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.IntermediateLists
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.Koszul

/-!
# One original remaining-diagonal list on the entire finite fiber

A single smooth diagonal list is chosen at the middle point of a fixed
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
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Modules.Pushforward

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (y : F.leftIntermediateImageProduct G H)

/-- Every point in the original full fiber has the fixed image-side middle point. -/
theorem leftFiberMiddlePoint (x : {w : F.leftIntermediateSupportProduct G H //
    F.leftIntermediateImageMap G H w = y}) :
    F.leftImageMiddlePair G H y = F.leftSupportMiddlePair G H x.1 := by
  exact (congrArg (F.leftImageMiddlePair G H) x.2.symm).trans
    (congrArg (fun m => m x.1) (F.leftIntermediateImageMap_middlePair G H))

/-- The only change in the middle stalk is its proved equality of original points. -/
def leftFiberMiddleStalkIso (x : {w : F.leftIntermediateSupportProduct G H //
    F.leftIntermediateImageMap G H w = y}) :
    (pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y) ≅
      (pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H x.1) :=
  (pullback h h).presheaf.stalkCongr (.of_eq (F.leftFiberMiddlePoint G H y x))

/-- The same fixed middle list at every original source-fiber point. -/
def leftFiberMiddleList
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)))
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = y}) :
    List ((pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H x.1)) :=
  s.map (F.leftFiberMiddleStalkIso G H y x).hom.hom

/-- The genuine common remaining list in the original image-side structure stalk. -/
def leftTargetRemainingList
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y))) :
    List ((F.leftIntermediateImageProduct G H).presheaf.stalk y) :=
  s.map ((F.leftImageMiddlePair G H).stalkMap y).hom

/-- The fixed target list acts on every original source through the literal
finite morphism and the actual equality identifying its image point. -/
@[reassoc] theorem leftFiberRemainingStalkMap
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = y}) :
    (F.leftImageMiddlePair G H).stalkMap y ≫
        Graph.alignedStalkMap (F.leftIntermediateImageMap G H) x.1 y x.2.symm =
      (F.leftFiberMiddleStalkIso G H y x).hom ≫
        (F.leftSupportMiddlePair G H).stalkMap x.1 := by
  rcases x with ⟨w, hw⟩
  subst y
  simp only [Graph.alignedStalkMap_rfl, leftFiberMiddleStalkIso,
    ← Scheme.Hom.stalkMap_comp]
  exact Scheme.Hom.stalkMap_congr_hom _ _ (F.leftIntermediateImageMap_middlePair G H) w

/-- One target list gives the actual support-middle image list simultaneously
at every original point of the full fiber. -/
theorem leftFiberRemainingList_map
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)))
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = y}) :
    (F.leftTargetRemainingList G H y s).map
        (Graph.alignedStalkMap (F.leftIntermediateImageMap G H) x.1 y x.2.symm).hom =
      (F.leftFiberMiddleList G H y s x).map
        ((F.leftSupportMiddlePair G H).stalkMap x.1).hom := by
  simp only [leftTargetRemainingList, leftFiberMiddleList, List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.leftFiberRemainingStalkMap G H y x) a

/-- The literal original ambient and finite-image routes carry the same fixed
list across the whole fiber, without any independently assumed source list. -/
theorem leftFiberRemainingList_square
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)))
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = y}) :
    (F.leftTargetRemainingList G H y s).map
        (Graph.alignedStalkMap (F.leftIntermediateImageMap G H) x.1 y x.2.symm).hom =
      ((F.leftFiberMiddleList G H y s x).map
        (F.leftAmbientMiddleStalkMap G H x.1).hom).map
          ((F.leftIntermediateAmbientInclusion G H).stalkMap x.1).hom :=
  (F.leftFiberRemainingList_map G H y s x).trans
    (F.leftAmbientMiddleList_map G H x.1 (F.leftFiberMiddleList G H y s x)).symm

private theorem stalkCongr_ideal {Q : Scheme.{u}} (J : Q.IdealSheafData)
    {z z' : Q} (e : z = z') (s : List (Q.presheaf.stalk z))
    (hs : J.stalk z = Ideal.ofList s) :
    J.stalk z' = Ideal.ofList (s.map (Q.presheaf.stalkCongr (.of_eq e)).hom.hom) := by
  subst z'
  simpa using hs

/-- The transported list still generates the very same original diagonal ideal,
now at each source point's equal middle point. -/
theorem leftFiberMiddleList_kernel
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)))
    (hs : (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H y) = Ideal.ofList s)
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = y}) :
    (pullback.diagonal h).ker.stalk (F.leftSupportMiddlePair G H x.1) =
      Ideal.ofList (F.leftFiberMiddleList G H y s x) :=
  stalkCongr_ideal (pullback.diagonal h).ker (F.leftFiberMiddlePoint G H y x) s hs

/-- Smoothness chooses one regular middle list at the fixed image-side point;
its length is local and no common smooth dimension is imposed. -/
theorem exists_leftTargetRemainingList [Smooth h] [IsSeparated h]
    (hy : ∃ z : Z, pullback.diagonal h z = F.leftImageMiddlePair G H y) :
    ∃ s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)),
      RingTheory.Sequence.IsRegular
        ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)) s ∧
      (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H y) = Ideal.ofList s := by
  obtain ⟨z, hz⟩ := hy
  have hex : ∃ s : List ((pullback h h).presheaf.stalk (pullback.diagonal h z)),
      RingTheory.Sequence.IsRegular
        ((pullback h h).presheaf.stalk (pullback.diagonal h z)) s ∧
      (pullback.diagonal h).ker.stalk (pullback.diagonal h z) = Ideal.ofList s := by
    obtain ⟨s, hs, hker⟩ := Diagonal.exists_regular_kernel_of_smooth h z
    exact ⟨s, hs, ((pullback.diagonal h).ker_stalk z).trans hker⟩
  exact (congrArg (fun q : (pullback h h : Scheme.{u}) =>
    ∃ s : List ((pullback h h).presheaf.stalk q),
      RingTheory.Sequence.IsRegular ((pullback h h).presheaf.stalk q) s ∧
        (pullback.diagonal h).ker.stalk q = Ideal.ofList s) hz).mp hex

omit y in
/-- An actual triple-incidence image lies over the actual remaining diagonal,
so the final geometric application supplies its own range witness. -/
theorem tripleImageMiddle_mem_diagonal (w : F.tripleIncidence G H) :
    ∃ z : Z, pullback.diagonal h z = F.leftImageMiddlePair G H
      (F.leftIntermediateImageMap G H (F.tripleIncidenceToLeftSupportProduct G H w)) := by
  refine ⟨F.incidenceTarget G (F.tripleIncidenceFst G H w), ?_⟩
  have he : (F.tripleIncidenceFst G H ≫ F.incidenceTarget G) ≫ pullback.diagonal h =
      F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftSupportMiddlePair G H :=
    (pullback_map_diagonal_isPullback (F.incidenceTarget G) H.projection h).w
  exact (congrArg (fun m => m w) he).trans
    (congrArg (fun m => m (F.tripleIncidenceToLeftSupportProduct G H w))
      (F.leftIntermediateImageMap_middlePair G H)).symm

omit y in
/-- At every actual triple image, smoothness constructs a single original
remaining list for the complete finite source fiber. -/
theorem exists_tripleImageRemainingList [Smooth h] [IsSeparated h]
    (w : F.tripleIncidence G H) :
    let y := F.leftIntermediateImageMap G H (F.tripleIncidenceToLeftSupportProduct G H w)
    ∃ s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)),
      RingTheory.Sequence.IsRegular
        ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H y)) s ∧
      (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H y) = Ideal.ofList s :=
  F.exists_leftTargetRemainingList G H _ (F.tripleImageMiddle_mem_diagonal G H w)

omit y in
/-- The all-fiber list square is exactly the original finite-affine Euler API,
including its original target point and source-stalk map. -/
theorem leftOriginalFiberRemainingList_map
    (V : (F.leftIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p}) :
    (F.leftTargetRemainingList G H (V.2.fromSpec p) s).map
        (FiniteEuler.originalFiberStalkMap (F.leftIntermediateImageMap G H) V.2 p x).hom =
      (F.leftFiberMiddleList G H (V.2.fromSpec p) s x).map
        ((F.leftSupportMiddlePair G H).stalkMap x.1).hom :=
  F.leftFiberRemainingList_map G H (V.2.fromSpec p) s x

end Motivic.FiniteCorrespondenceGenerator
