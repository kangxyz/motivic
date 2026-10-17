/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.SingularEndpoints
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus
public import Motivic.Algebra.Homology.SingularSetwisePaths
public import Lean.Util.CollectAxioms

/-! # Direct all-degree consumers of the actual algebraic-simplex prism -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.PresheafWithTransfers

universe u v

namespace MotivicTest.SingularEndpoints

variable (k : Type u) [Field k]

/-- Weight-one uses the original reduced torus and original singular chain complex. -/
def actualWeightOneHomotopy (U : SmoothSite (Spec (.of k))) :
    Homotopy (singularPrismEndpoint (reducedTorus k 1) U 0)
      (singularPrismEndpoint (reducedTorus k 1) U 1) :=
  singularPrismEndpointHomotopy (reducedTorus k 1) U

/-- This is an all-degree equality, not only a degree-zero relation. -/
theorem actualWeightOne_all_degrees (U : SmoothSite (Spec (.of k))) (n : ℕ) :
    HomologicalComplex.homologyMap (singularPrismEndpoint (reducedTorus k 1) U 0) n =
      HomologicalComplex.homologyMap (singularPrismEndpoint (reducedTorus k 1) U 1) n :=
  singularPrismEndpoint_homologyMap_eq (reducedTorus k 1) U n

/-- The same prism applies to every coefficient without assuming homotopy invariance. -/
def arbitraryCoefficientHomotopy (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) :
    Homotopy (singularPrismEndpoint P U 0) (singularPrismEndpoint P U 1) :=
  singularPrismEndpointHomotopy P U

open Lean in
run_cmd do
  for name in #[``SingularComplex.Prism.cut, ``SingularComplex.Prism.simplicialHomotopy,
      ``SingularComplex.Prism.endpointHomotopy,
      ``SingularComplex.Prism.boundary_of_cycle_path,
      ``SingularComplex.homologyMap_eq_zero_of_cycle_boundaries,
      ``SingularComplex.isZero_homology_of_normalized_cycle_paths,
      ``SingularComplex.normalized_cycle_faces,
      ``SingularComplex.isZero_homology_of_setwise_paths,
      ``SingularComplex.Prism.endpoint_homologyMap_eq,
      ``singularPrismEndpointHomotopy, ``singularPrismEndpoint_homologyMap_eq,
      ``actualWeightOneHomotopy, ``actualWeightOne_all_degrees,
      ``arbitraryCoefficientHomotopy] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-degree singular endpoint homotopies use only standard Lean foundations."

end MotivicTest.SingularEndpoints
