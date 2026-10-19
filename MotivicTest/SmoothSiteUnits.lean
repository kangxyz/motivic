/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Units.Basic
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Units.UnitComplex
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso
public import Motivic.Cohomology.SuslinVoevodsky.Hypercohomology
public import Lean.Util.CollectAxioms

/-! # Actual ordinary Gm in the motivic coefficient category -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SmoothSiteUnits

variable (k : Type u) [Field k]

/-- The genuine Gm sheaf has the same coefficient category as every original term. -/
def genuineGm :
    Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  SmoothSite.largeUnitsSheaf (Spec (.of k))

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Nisnevich.subcanonical,
      ``_root_.AlgebraicGeometry.Scheme.globalFunctionsRepresentable,
      ``_root_.AlgebraicGeometry.Scheme.globalFunctions_isSheaf,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.unitsPresheaf_isSheaf,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.unitsSheafSections,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.largeUnitsPresheaf_isSheaf,
      ``genuineGm, ``_root_.AlgebraicSimplex.constant_units_bijective,
      ``_root_.AlgebraicSimplex.constantUnitsEquiv_pullback,
      ``_root_.AlgebraicSimplex.constantUnitSimplicialIso,
      ``_root_.AlgebraicSimplex.unitChainHomotopyEquiv,
      ``_root_.AlgebraicSimplex.unitChainHomotopyEquiv_quasiIso,
      ``_root_.AlgebraicSimplex.schemeUnitChainHomotopyEquiv,
      ``_root_.AlgebraicSimplex.affineRelativeUnitChainHomotopyEquiv,
      ``_root_.AlgebraicSimplex.isIso_units_structureMap,
      ``_root_.AlgebraicSimplex.isIso_units_affineRelativeProjection,
      ``_root_.AlgebraicSimplex.isIso_units_affineSchemeProjection,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isIso_of_affine_app,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.integralAffineCover,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isIntegral_integralAffineCover_obj,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isIso_of_integral_affine_app,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.integralAffineInclusion_isCoverDense,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.extendIntegralAffineHom,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isIso_unitsSimplexPullback,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.simplexUnitsMap,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.unitSimplicialSheaf,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.constantUnitSimplicialSheafIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.unitSingularSheafHomotopyEquiv,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.unitSingularSheafHomotopyEquiv_quasiIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual global-unit Nisnevich sheaves use only standard Lean foundations."

end MotivicTest.SmoothSiteUnits
