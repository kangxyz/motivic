/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightImageIncidenceFiber
public import Motivic.AlgebraicGeometry.Correspondences.RightWholeFiberRemainingList
public import Motivic.AlgebraicGeometry.Intersection.RightWholeFiberTorRemainingSupport

/-!
# Genuine right remaining-Y Koszul finite length on every original finite-fiber branch

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

open Intersection

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [(correspondenceSixfoldAmbient f g h i).IsSeparated]
  [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (U : (F.rightIntermediateImageProduct G H).affineOpens)
  (y : F.rightImageIncidence G H)
  (hy : y ∈ genericPoints (F.rightImageIncidence G H))
  (hyU : F.rightImageIncidenceInclusion G H y ∈ U.1)
  (s : List ((pullback g g).presheaf.stalk
    (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))))
  (hs : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y)) = Ideal.ofList s)

include hy hyU hs in
/-- Genericity and finite remaining homology are derived on every original
source branch from the actual final image-incidence point and the one fixed list. -/
theorem rightWholeFiberTorRemainingFiber_finiteHomology
    (x : {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y}) (n : ℕ) :
    LengthEuler.FiniteHomology
      (Koszul.coefficientComplex (F.rightWholeFiberTorOriginalStalk G H U x.1 n)
        ((F.rightFiberMiddleList G H (F.rightImageIncidenceInclusion G H y) s x).map
          ((F.rightSupportMiddlePair G H).stalkMap x.1).hom)) := by
  rcases x with ⟨x, hx⟩
  obtain ⟨w, hw, _, hwx⟩ := F.rightImageIncidenceFiber_lift_generic G H y hy x hx
  subst x
  exact F.rightWholeFiberTorRemaining_finiteHomology G H U w
    (F.rightFiberMiddleList G H (F.rightImageIncidenceInclusion G H y) s ⟨_, hx⟩)
    (F.rightFiberMiddleList_kernel G H (F.rightImageIncidenceInclusion G H y) s hs ⟨_, hx⟩)
    hw (by change F.rightIntermediateImageMap G H _ ∈ U.1; rw [hx]; exact hyU) n

include hy hyU hs in
/-- The same all-branch result holds for genuine supported categorical Tor,
through its proved original-structure-stalk attachment to the actual coefficient. -/
theorem rightSupportedTorRemainingFiber_finiteHomology
    (x : {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y}) (n : ℕ) :
    LengthEuler.FiniteHomology
      (Koszul.coefficientComplex
        (closedIntersectionSupportedStalkTor (correspondenceSecondAmbientInclusion f g h i)
          (F.tripleSupportProductInclusion G H) (F.rightIntermediateSupportInclusion G H)
          (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
          x.1 n)
        ((F.rightFiberMiddleList G H (F.rightImageIncidenceInclusion G H y) s x).map
          ((F.rightSupportMiddlePair G H).stalkMap x.1).hom)) := by
  have hxU : x.1 ∈ (F.rightIntermediateImageMap G H) ⁻¹ᵁ U := by
    change F.rightIntermediateImageMap G H x.1 ∈ U.1
    rw [x.2]
    exact hyU
  let e := wholeFiberTorGluedStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) U x.1 hxU n
  exact (F.rightWholeFiberTorRemainingFiber_finiteHomology G H U y hy hyU s hs x n).of_iso
    (fun m => (HomologicalComplex.homologyFunctor _ _ m).mapIso (Koszul.coefficientIso e _))

include hy hyU in
/-- Smoothness supplies one original middle list at the final image-incidence
point, and it gives finite homology simultaneously on the entire source fiber. -/
theorem exists_rightWholeFiberTorRemainingFiber_finiteHomology [Smooth g] :
    ∃ s : List ((pullback g g).presheaf.stalk
      (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))),
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))) s ∧
      (pullback.diagonal g).ker.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y)) = Ideal.ofList s ∧
      ∀ (x : {x : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y}) (n : ℕ),
        LengthEuler.FiniteHomology
          (Koszul.coefficientComplex (F.rightWholeFiberTorOriginalStalk G H U x.1 n)
            ((F.rightFiberMiddleList G H (F.rightImageIncidenceInclusion G H y) s x).map
              ((F.rightSupportMiddlePair G H).stalkMap x.1).hom)) := by
  obtain ⟨s, hs, hker⟩ := F.exists_rightTargetRemainingList G H
    (F.rightImageIncidenceInclusion G H y) (F.rightImageIncidence_middle_mem_diagonal G H y)
  exact ⟨s, hs, hker,
    F.rightWholeFiberTorRemainingFiber_finiteHomology G H U y hy hyU s hker⟩

end Motivic.FiniteCorrespondenceGenerator
