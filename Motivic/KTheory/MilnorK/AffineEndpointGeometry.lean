/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Motivic.Aglib.AlgebraicGeometry.FiniteAffineEndpointBranches
public import Aglib.AlgebraicGeometry.DedekindPointStalk
public import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointNormEquality
public import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointBaseNorm
public import Aglib.KTheory.MilnorK.Dedekind.StalkResidue

/-! Exact original Milnor branch indexing and actual fiber residue-map consumers. -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open AlgebraicGeometry.FiniteAffineEndpointBranches
open MilnorK
open scoped Polynomial

universe u

namespace MilnorK.AffineEndpointGeometry

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


variable (E : Type u) [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]

omit [CharZero k] in
/-- The full scheme-theoretic fiber coefficient is the original field order. -/
theorem fundamentalCoefficient_eq_originalOrder (a : k) (x : fiber (baseMap S) a) :
    Motivic.IntegralCycle.toPoints (Motivic.fundamentalCycle (fiber (baseMap S) a)) x =
      MilnorK.K2.DVR.value
        (Localization.AtPrime
          (DedekindResidue.branchPoint k[X] S
            (PolynomialDedekindResidue.point (DedekindResidue.endpointPolynomial k a))
            (originalBranchEquiv k S a x)).asIdeal) E
        (Additive.ofMul (DedekindResidue.endpointParameter k E a)) := by
  let Q := DedekindResidue.branchPoint k[X] S
    (PolynomialDedekindResidue.point (DedekindResidue.endpointPolynomial k a))
    (originalBranchEquiv k S a x)
  have hs : algebraMap k[X] S (Polynomial.X - Polynomial.C a) ≠ 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff k[X] S).not.mpr (Polynomial.X_sub_C_ne_zero a)
  have h := DedekindStalkResidue.value_scalar_eq_stalkLength S E Q
    (algebraMap k[X] S (Polynomial.X - Polynomial.C a)) hs
  let : IsFinite (baseMap (k := k) S) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [fiber_fundamentalCoefficient, scalar_specMap]
  have hu : DedekindResidue.endpointParameter k E a =
      Units.mk0 (algebraMap S E (algebraMap k[X] S (Polynomial.X - Polynomial.C a)))
        ((map_ne_zero_iff (algebraMap S E) (IsFractionRing.injective S E)).mpr hs) := by
    apply Units.ext
    change algebraMap (RatFunc k) E
      (algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a)) =
      algebraMap S E (algebraMap k[X] S (Polynomial.X - Polynomial.C a))
    rw [← IsScalarTower.algebraMap_apply k[X] (RatFunc k) E,
      ← IsScalarTower.algebraMap_apply k[X] S E]
  rw [hu]
  exact h.symm

end MilnorK.AffineEndpointGeometry
