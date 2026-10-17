/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IncidenceCycle
public import Motivic.AlgebraicGeometry.Correspondences.CompositionSupportGraphs
public import Motivic.AlgebraicGeometry.Cycles.FundamentalClosedSubscheme

/-!
# Ordinary fundamental-cycle identity for genuine left-diagonal incidence

For an integral smooth source, its actual diagonal is one geometric generator.
Its actual left incidence is the original support scheme. Finite pushforward
of the full ordinary fundamental cycle therefore recovers the original cycle.
The target is allowed to be disconnected. This ordinary cycle calculation
alone makes no derived-intersection or full correspondence-category assertion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable (k : Type u) [Field k]
  {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The actual left-diagonal incidence fundamental correspondence is the original cycle. -/
theorem incidenceFundamentalCorrespondence_identity_left
    [IsIntegral ((𝟭 Scheme).obj X.left)] :
    (identityGenerator X.hom).incidenceFundamentalCorrespondence k A = A.cycle := by
  have : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  have : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [(identityGenerator X.hom).toIntegralCycle_incidenceFundamentalCorrespondence k]
  simp only [A.incidenceMap_identity_left, IntegralCycle.finitePushforward_comp]
  change IntegralCycle.finitePushforward A.inclusion
    (IntegralCycle.finitePushforward A.leftIdentityIncidenceIso.hom
      (fundamentalCycle ((identityGenerator X.hom).incidence A))) =
    FiniteCorrespondence.toIntegralCycle A.cycle
  rw [finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  change closedFundamentalCycle A.val =
    Finsupp.single A.toIntegralClosedSubscheme 1
  rw [closedFundamentalCycle_of_isIntegral]
  rfl

end Motivic.FiniteCorrespondenceGenerator
