/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteUnits
public import Motivic.AlgebraicGeometry.SmoothSiteUnitComplex
public import Motivic.AlgebraicGeometry.SmoothSiteIntegralAffineSheafIso
public import Motivic.Cohomology.Motivic.Hypercohomology
public import Lean.Util.CollectAxioms

/-! # Actual ordinary Gm in the motivic coefficient category -/

@[expose] public noncomputable section

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
  for name in #[``Nisnevich.subcanonical, ``globalFunctionsRepresentable,
      ``globalFunctions_isSheaf, ``SmoothSite.unitsPresheaf_isSheaf,
      ``SmoothSite.unitsSheafSections, ``SmoothSite.largeUnitsPresheaf_isSheaf,
      ``genuineGm, ``AlgebraicSimplex.constant_units_bijective,
      ``AlgebraicSimplex.constantUnitsEquiv_pullback,
      ``AlgebraicSimplex.constantUnitSimplicialIso,
      ``AlgebraicSimplex.unitChainHomotopyEquiv,
      ``AlgebraicSimplex.unitChainHomotopyEquiv_quasiIso,
      ``AlgebraicSimplex.schemeUnitChainHomotopyEquiv,
      ``AlgebraicSimplex.affineRelativeUnitChainHomotopyEquiv,
      ``AlgebraicSimplex.isIso_units_structureMap,
      ``AlgebraicSimplex.isIso_units_affineRelativeProjection,
      ``AlgebraicSimplex.isIso_units_affineSchemeProjection,
      ``SmoothSite.isIso_of_affine_app,
      ``SmoothSite.integralAffineCover,
      ``SmoothSite.isIntegral_integralAffineCover_obj,
      ``SmoothSite.isIso_of_integral_affine_app,
      ``SmoothSite.integralAffineInclusion_isCoverDense,
      ``SmoothSite.extendIntegralAffineHom,
      ``SmoothSite.isIso_unitsSimplexPullback,
      ``SmoothSite.simplexUnitsMap, ``SmoothSite.unitSimplicialSheaf,
      ``SmoothSite.constantUnitSimplicialSheafIso,
      ``SmoothSite.unitSingularSheafHomotopyEquiv,
      ``SmoothSite.unitSingularSheafHomotopyEquiv_quasiIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual global-unit Nisnevich sheaves use only standard Lean foundations."

end MotivicTest.SmoothSiteUnits
