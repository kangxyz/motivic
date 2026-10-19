/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.TorusDivisor
public import Lean.Util.CollectAxioms

/-! # Direct audit of the global ordinary norm from original torus correspondences -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates Motivic.SmoothSiteTorusDivisor
open  _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.SmoothSiteTorusDivisor

variable (k : Type u) [Field k]

def actual_global_norm : (toPresheaf k).obj (torusRepresentable k 1) ⟶
    SmoothSite.largeUnitsPresheaf (Spec (.of k)) := norm

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.scalarMap,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.sectionsAlgebra,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.sectionsMap,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.sectionsSmooth,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.sectionsNoetherian,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.isoSpec_inv_base,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.affineIso,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.affineIso_hom_left,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.affineIso_inv_left,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.affineIso_naturality,
          ``affineCycleCoordinates,
      ``affineCycleCoordinates_natural, ``affineNorm, ``affineNorm_natural,
      ``affinePowerOneNorm, ``affinePowerOneNorm_natural, ``largeAffineNorm,
      ``integralAffineNorm, ``norm, ``norm_app, ``actual_global_norm] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original torus ordinary global-unit map uses only standard Lean foundations."

end MotivicTest.SmoothSiteTorusDivisor
