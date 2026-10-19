/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.WholeFiberTorRemainingList
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Actual smooth-site whole-coefficient remaining-list consumers

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

namespace MotivicTest.WholeFiberRemainingList

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

/-- A single actual smooth diagonal list is chosen once at the final triple
image; every original source branch receives its true whole-coefficient
remaining Koszul comparison, in all outer Tor degrees. -/
theorem actualSmoothWholeFiberRemainingList (w : F.tripleIncidence G H)
    (hp : V.2.fromSpec p =
      F.leftIntermediateImageMap G H (F.tripleIncidenceToLeftSupportProduct G H w)) :
    ∃ s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))),
      RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))) s ∧
      (pullback.diagonal Z.hom).ker.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p)) =
        Ideal.ofList s ∧
      ∀ (x : {x : F.leftIntermediateSupportProduct G H //
          F.leftIntermediateImageMap G H x = V.2.fromSpec p}) (n : ℕ),
        Nonempty (_root_.ChainComplex.Koszul.coefficientComplex
          (F.firstStageWholeOriginalStalkModule (S := Spec (.of K)) G H V p x n)
          ((F.leftTargetRemainingList G H (V.2.fromSpec p) s).map
            (originalFiberStalkMap (F.leftIntermediateImageMap G H) V.2 p x).hom) ≅
          _root_.ChainComplex.Koszul.coefficientComplex (F.firstStageSupportedStalkTor (S :=
              Spec (.of K)) G H x.1 n)
            ((F.leftFiberMiddleList G H (V.2.fromSpec p) s x).map
              ((F.leftSupportMiddlePair G H).stalkMap x.1).hom)) := by
  have hy : ∃ z : Z.left, pullback.diagonal Z.hom z =
      F.leftImageMiddlePair G H (V.2.fromSpec p) := by
    rw [hp]
    exact F.tripleImageMiddle_mem_diagonal G H w
  obtain ⟨s, hs, hker⟩ := F.exists_leftTargetRemainingList G H (V.2.fromSpec p) hy
  refine ⟨s, hs, hker, ?_⟩
  intro x n
  exact ⟨F.firstStageWholeRemainingStalkIso (S := Spec (.of K)) G H V p s x n⟩

/-- The actual coordinate action on the whole finite inverse image. -/
local instance actualCoordinateAlgebra :
    Algebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.leftIntermediateImageMap G H).app V).hom.toAlgebra

/-- Every original point of the complete source fiber is represented by a
maximal point of the single whole finite algebra used by the actual coefficient. -/
theorem actualWholeRemainingCoversFiber
    (x : {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = V.2.fromSpec p}) :
    ∃ q : MaximalSpectrum (localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p),
      wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q = x :=
  (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p).surjective x

/-- The true whole-section coefficient and common target list feed the actual
localized remaining Koszul complex, with original geometric supported Tor as target. -/
def actualSmoothWholeRemainingLocalizedIso
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (q : MaximalSpectrum (localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p))
    (n : ℕ) :=
  F.firstStageWholeRemainingLocalizedIso (S := Spec (.of K)) G H V p q s n

/-- The original six-factor remaining equations act on the genuine coefficient
through exactly the original ambient-to-support structure-stalk map. -/
def actualSmoothWholeRemainingAmbientListIso
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (x : {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = V.2.fromSpec p}) (n : ℕ) :=
  F.firstStageWholeRemainingAmbientListIso (S := Spec (.of K)) G H V p s x n

/-- All original stalk scalars remain explicit in the actual homology comparison. -/
def actualSmoothWholeRemainingHomologyIso
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (x : {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = V.2.fromSpec p}) (n r : ℕ) :=
  F.firstStageWholeRemainingHomologyIso (S := Spec (.of K)) G H V p s x n r

end MotivicTest.WholeFiberRemainingList
