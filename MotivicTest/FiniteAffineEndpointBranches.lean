/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Aglib.AlgebraicGeometry.FiniteAffineEndpointBranches
import Aglib.AlgebraicGeometry.DedekindPointStalk
import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointNormEquality
import Lean.Util.CollectAxioms

/-! Exact original Milnor branch indexing and actual fiber residue-map consumers. -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open AlgebraicGeometry.FiniteAffineEndpointBranches
open MilnorK
open scoped Polynomial

universe u

namespace MotivicTest.FiniteAffineEndpointBranches

variable (k S : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S]
  [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S]

attribute [local instance] Classical.decEq DedekindResidue.polynomialPointResidueCharZero

/-- The endpoint sum's exact original ideal branches index the actual fiber. -/
def originalBranchEquiv (a : k) :
    fiber (Spec.map (CommRingCat.ofHom (algebraMap k[X] S))) a ≃
      AdicCompletion.IdealBranch
        ((PolynomialDedekindResidue.point (DedekindResidue.endpointPolynomial k a)).asIdeal.map
          (algebraMap k[X] S)) :=
  pointEquiv S a

omit [CharZero k] in
/-- The original Milnor branch prime is literally the actual ambient fiber point. -/
theorem originalBranchPoint (a : k) (x : fiber (baseMap S) a) :
    DedekindPointStalk.point
        (DedekindResidue.branchPoint k[X] S
          (PolynomialDedekindResidue.point (DedekindResidue.endpointPolynomial k a))
          (originalBranchEquiv k S a x)) =
      fiberInclusion (baseMap S) a x := rfl

/-- Both actual residue maps compose without changing the original prime. -/
def originalBranchResidueEquiv (a : k) (x : fiber (baseMap S) a) :
    IsLocalRing.ResidueField
        (Localization.AtPrime
          (DedekindResidue.branchPoint k[X] S
            (PolynomialDedekindResidue.point (DedekindResidue.endpointPolynomial k a))
            (originalBranchEquiv k S a x)).asIdeal) ≃+*
      (fiber (baseMap S) a).residueField x :=
  (DedekindPointStalk.residueEquiv _).trans (fiberResidueEquiv S a x)

omit [CharZero k] in
/-- The original scalar, localization, stalk and fiber maps form a commuting square. -/
theorem originalBranchResidueEquiv_scalar (a : k) (x : fiber (baseMap S) a) (s : S) :
    originalBranchResidueEquiv k S a x
        (IsLocalRing.residue _ (algebraMap S _ s)) =
      IsLocalRing.residue ((fiber (baseMap S) a).presheaf.stalk x)
        ((fiberInclusion (baseMap S) a).stalkMap x
          (StructureSheaf.toStalk S (fiberInclusion (baseMap S) a x) s)) := by
  rw [originalBranchResidueEquiv, RingEquiv.trans_apply,
    DedekindPointStalk.residueEquiv_algebraMap]
  exact fiberResidueEquiv_scalar S a x s

end MotivicTest.FiniteAffineEndpointBranches

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `AlgebraicGeometry.FiniteAffineEndpointBranches.pointEquiv,
    `AlgebraicGeometry.FiniteAffineEndpointBranches.pointEquiv_symm_point,
    `AlgebraicGeometry.FiniteAffineEndpointBranches.fiberResidueEquiv,
    `AlgebraicGeometry.FiniteAffineEndpointBranches.fiberResidueEquiv_scalar,
    `AlgebraicGeometry.FiniteAffineEndpointBranches.fiberResidueEquiv_Γevaluation,
    `MotivicTest.FiniteAffineEndpointBranches.originalBranchEquiv,
    `MotivicTest.FiniteAffineEndpointBranches.originalBranchPoint,
    `MotivicTest.FiniteAffineEndpointBranches.originalBranchResidueEquiv,
    `MotivicTest.FiniteAffineEndpointBranches.originalBranchResidueEquiv_scalar]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} actual endpoint branch and residue-map declarations: \
    standard axioms only."
