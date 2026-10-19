/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Cycle
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Graphs
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.ClosedSubscheme

/-!
# Consumers of degree-weighted incidence-cycle assembly

These consumers retain arbitrary fields, disconnected smooth objects,
nonreduced incidence, and collisions between finite component images. A
right-identity incidence calculation recovers the original geometric cycle
from the actual ordinary fundamental cycle and its finite pushforward.
No theorem here identifies ordinary local lengths with derived intersections.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (closedFundamentalCycle closedFundamentalCycle_of_isIntegral
  finitePushforward_fundamentalCycle fundamentalCycle isNoetherian_of_finiteType)
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic
open scoped BigOperators

universe u

namespace MotivicTest.IncidenceCycle

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Finiteness follows from the actual geometry, without an input enumeration. -/
theorem actual_incidence_generics_finite : (genericPoints (A.incidence B)).Finite :=
  A.finite_incidence_genericPoints k B

/-- Arbitrary integer input coefficients assemble additively on actual smooth generators. -/
noncomputable def actualAssembly :
    (genericPoints (A.incidence B) → ℤ) →+ FiniteCorrespondence X.hom Z.hom :=
  A.incidenceCycleAssembly k B

/-- Actual residue degrees, finite images, and coefficient collisions survive forgetting. -/
theorem assembly_is_actual_pushforward (c : genericPoints (A.incidence B) → ℤ) :
    FiniteCorrespondence.toIntegralCycle (actualAssembly k A B c) =
      IntegralCycle.finitePushforward (A.incidenceMap B)
        (IntegralCycle.ofGenericCoefficients (A.incidence B) c) :=
  A.toIntegralCycle_incidenceCycleAssembly k B c

open Classical in
/-- A coefficient sums every component mapping to this actual image, rather than choosing one. -/
theorem image_collisions_sum (c : genericPoints (A.incidence B) → ℤ)
    (V : FiniteCorrespondenceGenerator X.hom Z.hom) :
    A.incidenceCycleAssembly k B c V =
      letI := IntegralCycle.genericPointFintype (A.incidence B)
      ∑ x, if A.smoothIncidenceComponentGenerator k B x = V then
        c x * ((A.incidenceMap B).residueDegree x.val : ℤ) else 0 :=
  A.incidenceCycleAssembly_coefficient k B c V

/-- The genuine nonreduced incidence's ordinary local lengths recover its
fundamental pushforward. -/
theorem ordinary_fundamental_pushforward :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (A.incidenceFundamentalCorrespondence k B) =
      IntegralCycle.finitePushforward (A.incidenceMap B) (fundamentalCycle (A.incidence B)) :=
  A.toIntegralCycle_incidenceFundamentalCorrespondence k B

/-- For actual right-diagonal incidence the ordinary fundamental pushforward is the
original geometric generator with coefficient one. The source may remain disconnected. -/
theorem right_identity_fundamental_cycle [IsIntegral ((𝟭 Scheme).obj Y.left)] :
    A.incidenceFundamentalCorrespondence k (identityGenerator Y.hom) = A.cycle := by
  have : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  have : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [A.toIntegralCycle_incidenceFundamentalCorrespondence k]
  simp only [A.incidenceMap_identity_right, IntegralCycle.finitePushforward_comp]
  change IntegralCycle.finitePushforward A.inclusion
    (IntegralCycle.finitePushforward A.rightIdentityIncidenceIso.hom
      (fundamentalCycle (A.incidence (identityGenerator Y.hom)))) =
    FiniteCorrespondence.toIntegralCycle A.cycle
  rw [finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  change closedFundamentalCycle A.val =
    Finsupp.single A.toIntegralClosedSubscheme 1
  rw [closedFundamentalCycle_of_isIntegral]
  rfl

end MotivicTest.IncidenceCycle
