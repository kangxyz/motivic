/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.RightWholeFiberTorRemainingList
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Actual right smooth-site whole-coefficient remaining-Y consumers

Over an arbitrary field, one list is constructed at an actual triple image.
The same choice attaches the actual whole Tor coefficient to every original
source-fiber stalk. Its maximal-localization consumer uses the whole original
finite algebra, including every branch, with no fixed smooth dimension.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.PrimeSpectrum.FiniteFiber (localAlgebra)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorRemainingList

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- A single actual smooth diagonal list is chosen once at the final triple
image; every original source branch receives its true whole-coefficient
remaining Koszul comparison, in all outer Tor degrees. -/
theorem actualSmoothWholeFiberRemainingList (w : F.tripleIncidence G H)
    (hp : V.2.fromSpec p =
      F.rightIntermediateImageMap G H (F.tripleIncidenceToRightSupportProduct G H w)) :
    ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))) s ∧
      (pullback.diagonal Y.hom).ker.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p)) =
        Ideal.ofList s ∧
      ∀ (x : {x : F.rightIntermediateSupportProduct G H //
          F.rightIntermediateImageMap G H x = V.2.fromSpec p}) (n : ℕ),
        Nonempty (_root_.ChainComplex.Koszul.coefficientComplex
          (F.rightFirstStageWholeOriginalStalkModule (S := Spec (.of K)) G H V p x n)
          ((F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
            (originalFiberStalkMap (F.rightIntermediateImageMap G H) V.2 p x).hom) ≅
          _root_.ChainComplex.Koszul.coefficientComplex
            (F.rightFirstStageSupportedStalkTor (S := Spec (.of K)) G H x.1 n)
            ((F.rightFiberMiddleList G H (V.2.fromSpec p) s x).map
              ((F.rightSupportMiddlePair G H).stalkMap x.1).hom)) := by
  have hy : ∃ z : Y.left, pullback.diagonal Y.hom z =
      F.rightImageMiddlePair G H (V.2.fromSpec p) := by
    rw [hp]
    exact F.rightTripleImageMiddle_mem_diagonal G H w
  obtain ⟨s, hs, hker⟩ := F.exists_rightTargetRemainingList G H (V.2.fromSpec p) hy
  refine ⟨s, hs, hker, ?_⟩
  intro x n
  exact ⟨F.rightFirstStageWholeRemainingStalkIso (S := Spec (.of K)) G H V p s x n⟩

/-- The actual coordinate action on the whole finite inverse image. -/
local instance actualCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

/-- Every original point of the complete source fiber is represented by a
maximal point of the single whole finite algebra used by the actual coefficient. -/
theorem actualWholeRemainingCoversFiber
    (x : {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = V.2.fromSpec p}) :
    ∃ q : MaximalSpectrum (localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p),
      wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q = x :=
  (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p).surjective x

/-- The true whole-section coefficient and common target list feed the actual
localized remaining Koszul complex, with original geometric supported Tor as target. -/
def actualSmoothWholeRemainingLocalizedIso
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (q : MaximalSpectrum (localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p))
    (n : ℕ) :=
  F.rightFirstStageWholeRemainingLocalizedIso (S := Spec (.of K)) G H V p q s n

/-- The original six-factor remaining equations act on the genuine coefficient
through exactly the original ambient-to-support structure-stalk map. -/
def actualSmoothWholeRemainingAmbientListIso
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = V.2.fromSpec p}) (n : ℕ) :=
  F.rightFirstStageWholeRemainingAmbientListIso (S := Spec (.of K)) G H V p s x n

/-- All original stalk scalars remain explicit in the actual homology comparison. -/
def actualSmoothWholeRemainingHomologyIso
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = V.2.fromSpec p}) (n r : ℕ) :=
  F.rightFirstStageWholeRemainingHomologyIso (S := Spec (.of K)) G H V p s x n r

end Motivic.MotivicTest.RightWholeFiberTorRemainingList
