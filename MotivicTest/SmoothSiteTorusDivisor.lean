/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteTorusDivisor
public import Lean.Util.CollectAxioms

/-! # Direct audit of the global ordinary norm from original torus correspondences -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.SmoothSiteAffineCoordinates Motivic.SmoothSiteTorusDivisor
open Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.SmoothSiteTorusDivisor

variable (k : Type u) [Field k]

def actual_global_norm : (toPresheaf k).obj (torusRepresentable k 1) ⟶
    SmoothSite.largeUnitsPresheaf (Spec (.of k)) := norm

open Lean in
run_cmd do
  for name in #[``scalarMap, ``sectionsAlgebra, ``sectionsMap, ``sectionsSmooth,
      ``sectionsNoetherian, ``isoSpec_inv_base, ``affineIso, ``affineIso_hom_left,
      ``affineIso_inv_left, ``affineIso_naturality, ``affineCycleCoordinates,
      ``affineCycleCoordinates_natural, ``affineNorm, ``affineNorm_natural,
      ``affinePowerOneNorm, ``affinePowerOneNorm_natural, ``largeAffineNorm,
      ``integralAffineNorm, ``norm, ``norm_app, ``actual_global_norm] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original torus ordinary global-unit map uses only standard Lean foundations."

end MotivicTest.SmoothSiteTorusDivisor
