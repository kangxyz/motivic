/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorChart
public import Motivic.AlgebraicGeometry.Intersection.ExteriorKoszulTorSupport

/-!
# Actual first-stage affine Tor coefficient sheaves

Each original six-factor affine neighborhood gives an actual coefficient module
and quasi-coherent sheaf on its whole closed inverse image. Finite generation
is derived from the four original finite-type structure maps. No global Tor
coefficient, transition or cocycle is assumed or constructed by these consumers.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace Motivic.MotivicTest.ClosedIntersectionTorChart

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S} [IsSeparated g]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The genuine first-stage affine coefficient over the original support section ring. -/
def firstStageCoefficient (U : (correspondenceSixfoldAmbient f g h i).affineOpens) (n : ℕ) :
    ModuleCat Γ(F.leftIntermediateSupportProduct G H,
      (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U) :=
  closedIntersectionAffineTor (F.tripleSupportProductInclusion G H)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediate_ambient_isPullback G H) U n

/-- Its ambient restriction is the actual categorical Tor of both literal section quotients. -/
def firstStageAmbientIso (U : (correspondenceSixfoldAmbient f g h i).affineOpens) (n : ℕ) :=
  closedIntersectionAffineTorAmbientIso (F.tripleSupportProductInclusion G H)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediate_ambient_isPullback G H) U n

/-- Actual locally finite-type geometry gives finite coefficients in every degree. -/
theorem firstStageCoefficient_finite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i]
    (U : (correspondenceSixfoldAmbient f g h i).affineOpens) (n : ℕ) :
    Module.Finite Γ(F.leftIntermediateSupportProduct G H,
      (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U) (firstStageCoefficient F G H U n) := by
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact inferInstanceAs (Module.Finite _
    (closedIntersectionAffineTor (F.tripleSupportProductInclusion G H)
      (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
      (correspondenceFirstDiagonalInclusion f g h i)
      (F.leftIntermediate_ambient_isPullback G H) U n))

/-- Tilde constructs a real sheaf on each actual first-stage closed affine inverse image. -/
def firstStageChartSheaf (U : (correspondenceSixfoldAmbient f g h i).affineOpens) (n : ℕ) :=
  closedIntersectionTorChartSheaf (F.tripleSupportProductInclusion G H)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediate_ambient_isPullback G H) U n

/-- The local first-stage sheaf has proved quasi-coherence, not a supplied QC premise. -/
theorem firstStageChartSheaf_quasicoherent
    (U : (correspondenceSixfoldAmbient f g h i).affineOpens) (n : ℕ) :
    (firstStageChartSheaf F G H U n).IsQuasicoherent :=
  closedIntersectionTorChartSheaf_quasicoherent _ _ _ _ _ _ _

end Motivic.MotivicTest.ClosedIntersectionTorChart
