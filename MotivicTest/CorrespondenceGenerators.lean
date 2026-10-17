/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Generators

/-!
# Consumers of geometric correspondence generators

These tests use actual graph subschemes and geometric multiplicities. They
include affine integral sources, rather than accepting a graph theorem as an
unproved parameter. No composition law for cycles is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorrespondenceGenerators

variable {S X Y : Scheme.{u}} (φ : X ⟶ Y) (g : Y ⟶ S)
variable [IsIntegral X] [IsSeparated g]

/-- The graph is nonzero as a genuine geometric cycle. -/
theorem graphCycle_ne_zero : graphCycle φ g ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun c : FiniteCorrespondence (φ ≫ g) g =>
    c (graphGenerator φ g)) h
  simp at hcoeff

/-- The graph's constructed integral subscheme projects onto its source. -/
example : Function.Surjective (graphGenerator φ g).projection :=
  (graphGenerator φ g).projection_surjective

/-- After identifying the graph with its source, its target map is the original map. -/
example : (correspondenceGraph φ g).toImage ≫ (graphGenerator φ g).inclusion ≫
    pullback.snd (φ ≫ g) g = φ := by
  simp [graphGenerator, FiniteCorrespondenceGenerator.inclusion, correspondenceGraphIdeal]

/-- The identity graph exists for every affine integral scheme. -/
example (R : Type u) [CommRing R] [IsDomain R] :
    graphCycle (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R))) ≠ 0 :=
  graphCycle_ne_zero _ _

/-- Free geometric cycles distinguish different integral closed supports. -/
example {f : X ⟶ S} (Z W : FiniteCorrespondenceGenerator f g) (h : Z ≠ W) :
    Z.cycle ≠ W.cycle := fun he => h (FiniteCorrespondenceGenerator.cycle_injective he)

end MotivicTest.CorrespondenceGenerators
