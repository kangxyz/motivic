/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorDescent

/-!
# Actual six-factor Tor descent consumers

These consumers use the genuine first middle diagonal and the original
three-support exterior inclusion. Every transition and common-open cocycle
is constructed, with ambient separatedness derived from the structure maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.Intersection
open Motivic.FiniteOpenModuleGluing

universe u

namespace Motivic.MotivicTest.ClosedIntersectionTorDescent

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S} [S.IsSeparated]
  [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable {ι : Type u} (U : ι → (correspondenceSixfoldAmbient f g h i).affineOpens)

/-- A genuine datum for arbitrary original six-factor affine charts, with no supplied laws. -/
def actualSixfoldDatum (n : ℕ) :
    Datum (fun r => (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U r)
      (fun r => closedIntersectionTorChartSheaf (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediate_ambient_isPullback G H) (U r) n) :=
  closedIntersectionTorDatum (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H) U n

/-- The actual first-stage Tor transition satisfies the full common-smaller-open cocycle. -/
theorem actualSixfoldCocycle (n : ℕ)
    (O : (F.leftIntermediateSupportProduct G H).Opens) (r s t : ι)
    (hr : O ≤ (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U r)
    (hs : O ≤ (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U s)
    (ht : O ≤ (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U t) :
    transitionOn _ _ (actualSixfoldDatum F G H U n).transition r s hr hs ≪≫
      transitionOn _ _ (actualSixfoldDatum F G H U n).transition s t hs ht =
        transitionOn _ _ (actualSixfoldDatum F G H U n).transition r t hr ht :=
  (actualSixfoldDatum F G H U n).cocycle O r s t hr hs ht

/-- The constructed relative six-factor coefficient is quasi-coherent on the entire chosen union. -/
theorem actualSixfoldCoefficient_quasicoherent [Fintype ι]
    (V : (F.leftIntermediateSupportProduct G H).Opens)
    (hU : ⨆ r, (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U r = V) (n : ℕ) :
    (closedIntersectionTorCoefficient (F.tripleSupportProductInclusion G H)
      (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
      (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
      U V n).IsQuasicoherent :=
  closedIntersectionTorCoefficient_quasicoherent _ _ _ _ _ U V hU n

/-- Empty families are admitted; the empty union receives its actual quasi-coherent coefficient. -/
theorem actualEmptyCoefficient_quasicoherent (n : ℕ) :
    (closedIntersectionTorCoefficient (F.tripleSupportProductInclusion G H)
      (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
      (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
      (fun r : ULift.{u} (Fin 0) => r.down.elim0) ⊥ n).IsQuasicoherent :=
  closedIntersectionTorCoefficient_quasicoherent _ _ _ _ _ _ ⊥ (by simp) n

end Motivic.MotivicTest.ClosedIntersectionTorDescent
