/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedAffineCover
public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalAmbient

/-!
# Actual affine overlaps in the separated six-factor ambient

Affine intersections require a separated ambient. This leaf derives that
property from the genuine separated structure maps over a separated base.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ClosedAffineCover

variable {P : Scheme.{u}} [P.IsSeparated]

/-- The actual intersection of two affine ambient opens is affine by separatedness. -/
def affineOverlap (U V : P.affineOpens) : P.affineOpens :=
  ⟨U.1 ⊓ V.1, U.2.inf V.2⟩

/-- The left inclusion of the true affine ambient overlap. -/
theorem affineOverlap_le_left (U V : P.affineOpens) : affineOverlap U V ≤ U := by
  change U.1 ⊓ V.1 ≤ U.1
  exact inf_le_left

/-- The right inclusion of the true affine ambient overlap. -/
theorem affineOverlap_le_right (U V : P.affineOpens) : affineOverlap U V ≤ V := by
  change U.1 ⊓ V.1 ≤ V.1
  exact inf_le_right

/-- The actual closed-chart overlap is the inverse image of the true ambient intersection. -/
theorem preimage_affineOverlap {X : Scheme.{u}} (j : X ⟶ P) (U V : P.affineOpens) :
    j ⁻¹ᵁ (affineOverlap U V).1 = (j ⁻¹ᵁ U) ⊓ (j ⁻¹ᵁ V) :=
  j.preimage_inf

end Motivic.ClosedAffineCover

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]

/-- The genuine six-factor ambient is separated, derived from its original structure maps. -/
theorem correspondenceSixfoldAmbient_isSeparated :
    (correspondenceSixfoldAmbient f g h i).IsSeparated := by
  let a : correspondenceSixfoldAmbient f g h i ⟶ S :=
    pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
      correspondenceAmbientTarget f g h ≫ h
  have ha : IsSeparated a := by
    dsimp [a, correspondenceAmbientTarget, correspondenceIntersectionAmbient]
    infer_instance
  refine ⟨?_⟩
  rw [← terminal.comp_from a]
  infer_instance

/-- Actual six-factor affine intersections are affine.
This is not asserted for arbitrary schemes. -/
theorem correspondenceSixfoldAffineOverlap
    (U V : (correspondenceSixfoldAmbient f g h i).affineOpens) :
    IsAffineOpen (U.1 ⊓ V.1) := by
  let := correspondenceSixfoldAmbient_isSeparated f g h i
  exact U.2.inf V.2

end Motivic
