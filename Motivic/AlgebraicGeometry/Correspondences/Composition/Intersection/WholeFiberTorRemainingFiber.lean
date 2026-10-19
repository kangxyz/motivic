/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.IntermediateImageFiber
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.WholeFiber.RemainingList
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.WholeFiberTorRemainingSupport

/-!
# Genuine remaining Koszul finite length on every original finite-fiber branch

At a generic point of the actual final incidence on the intermediate scheme
image, the whole ambient source fiber lifts to generic points of original
triple incidence. One middle-diagonal list is chosen at that fixed target
point and transported by the original stalk maps. The constructed whole-fiber
Tor coefficient and its actual supported-Tor stalk therefore have finite
remaining Koszul homology on every branch, in all first-stage Tor degrees.
No source genericity, local finite length, or point-lift premise is supplied.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [IsSeparated g] [IsSeparated h]
  [(correspondenceSixfoldAmbient f g h i).IsSeparated]
  [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (U : (F.leftIntermediateImageProduct G H).affineOpens)
  (y : F.leftImageIncidence G H)
  (hy : y ∈ genericPoints (F.leftImageIncidence G H))
  (hyU : F.leftImageIncidenceInclusion G H y ∈ U.1)
  (s : List ((pullback h h).presheaf.stalk
    (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y))))
  (hs : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y)) = Ideal.ofList s)

include hy hyU hs in
/-- Genericity and finite remaining homology are derived on every original
source branch from the actual final image-incidence point and the one fixed list. -/
theorem leftWholeFiberTorRemainingFiber_finiteHomology
    (x : {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y}) (n : ℕ) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
      (_root_.ChainComplex.Koszul.coefficientComplex (F.leftWholeFiberTorOriginalStalk G H U x.1 n)
        ((F.leftFiberMiddleList G H (F.leftImageIncidenceInclusion G H y) s x).map
          ((F.leftSupportMiddlePair G H).stalkMap x.1).hom)) := by
  rcases x with ⟨x, hx⟩
  obtain ⟨w, hw, _, hwx⟩ := F.leftImageIncidenceFiber_lift_generic G H y hy x hx
  subst x
  exact F.leftWholeFiberTorRemaining_finiteHomology G H U w
    (F.leftFiberMiddleList G H (F.leftImageIncidenceInclusion G H y) s ⟨_, hx⟩)
    (F.leftFiberMiddleList_kernel G H (F.leftImageIncidenceInclusion G H y) s hs ⟨_, hx⟩)
    hw (by change F.leftIntermediateImageMap G H _ ∈ U.1; rw [hx]; exact hyU) n

include hy hyU hs in
/-- The same all-branch result holds for genuine supported categorical Tor,
through its proved original-structure-stalk attachment to the actual coefficient. -/
theorem leftSupportedTorRemainingFiber_finiteHomology
    (x : {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y}) (n : ℕ) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
      (_root_.ChainComplex.Koszul.coefficientComplex
        (closedIntersectionSupportedStalkTor (correspondenceFirstDiagonalInclusion f g h i)
          (F.tripleSupportProductInclusion G H) (F.leftIntermediateSupportInclusion G H)
          (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
          x.1 n)
        ((F.leftFiberMiddleList G H (F.leftImageIncidenceInclusion G H y) s x).map
          ((F.leftSupportMiddlePair G H).stalkMap x.1).hom)) := by
  have hxU : x.1 ∈ (F.leftIntermediateImageMap G H) ⁻¹ᵁ U := by
    change F.leftIntermediateImageMap G H x.1 ∈ U.1
    rw [x.2]
    exact hyU
  let e := wholeFiberTorGluedStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) U x.1 hxU n
  exact (F.leftWholeFiberTorRemainingFiber_finiteHomology G H U y hy hyU s hs x n).of_iso
    (fun m => (HomologicalComplex.homologyFunctor _ _ m).mapIso
        (_root_.ChainComplex.Koszul.coefficientIso e _))

include hy hyU in
/-- Smoothness supplies one original middle list at the final image-incidence
point, and it gives finite homology simultaneously on the entire source fiber. -/
theorem exists_leftWholeFiberTorRemainingFiber_finiteHomology [Smooth h] :
    ∃ s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y))),
      RingTheory.Sequence.IsRegular ((pullback h h).presheaf.stalk
        (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y))) s ∧
      (pullback.diagonal h).ker.stalk
        (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y)) = Ideal.ofList s ∧
      ∀ (x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y}) (n : ℕ),
        _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
          (_root_.ChainComplex.Koszul.coefficientComplex (F.leftWholeFiberTorOriginalStalk G H U x.1
              n)
            ((F.leftFiberMiddleList G H (F.leftImageIncidenceInclusion G H y) s x).map
              ((F.leftSupportMiddlePair G H).stalkMap x.1).hom)) := by
  obtain ⟨s, hs, hker⟩ := F.exists_leftTargetRemainingList G H
    (F.leftImageIncidenceInclusion G H y) (F.leftImageIncidence_middle_mem_diagonal G H y)
  exact ⟨s, hs, hker,
    F.leftWholeFiberTorRemainingFiber_finiteHomology G H U y hy hyU s hker⟩

end Motivic.FiniteCorrespondenceGenerator
