/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.ReducedTorusExact
public import Lean.Util.CollectAxioms

/-! # Direct audit of the actual reduced divisor short exact sequence -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic Opposite
open Motivic.SmoothSiteTorusDivisor Motivic.SmoothSiteBoundaryOneDivisor
open Motivic.SmoothSiteReducedTorusExact

universe u

namespace MotivicTest.SmoothSiteReducedTorusExact

variable {k : Type u} [Field k]

/-- The consumer uses exactly the original reduced sections and global units. -/
def actual_local_sequence (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] : ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk (largeAffineReducedDivisor k X) (reducedNorm.app (op X))
    (largeAffineReducedDivisor_reducedNorm X)

/-- All three places of the actual local sequence are tested as a genuine short exact sequence. -/
theorem actual_local_shortExact (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] : (actual_local_sequence X).ShortExact where
  exact := (ShortComplex.ab_exact_iff _).mpr fun z hz =>
    (reducedNorm_app_eq_zero_iff X z).mp hz
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (largeAffineReducedDivisor_injective X)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (reducedNorm_app_surjective X)

open Lean in
run_cmd do
  for name in #[``powerOneTargetEquiv, ``affinePowerOneRationalEquiv, ``identityGraph,
      ``affinePowerOneRationalEquiv_identityGraph,
      ``affinePowerOneRationalEquiv_affinePowerOneDivisor,
      ``affinePowerOneNorm_kernel_decomposition, ``affinePowerOneNorm_surjective,
      ``affinePowerOneDivisor_identityGraph_intersection, ``toReduced_identityGraph,
      ``toReduced_add_identityGraph, ``toReduced_eq_zero_iff,
      ``affinePowerOneNorm_affinePowerOneDivisor, ``largeAffineReducedDivisor_reducedNorm,
      ``largeAffineReducedDivisor_injective, ``reducedNorm_app_surjective,
      ``reducedNorm_app_eq_zero_iff, ``actual_local_sequence, ``actual_local_shortExact] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual reduced divisor short exact sequence uses only standard Lean foundations."

end MotivicTest.SmoothSiteReducedTorusExact
