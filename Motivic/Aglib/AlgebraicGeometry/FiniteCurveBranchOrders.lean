/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteCurveNormalization
public import Aglib.RingTheory.DVRCartierLength
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Actual normalization branches and endpoint orders

The endpoint equation is the image of the original polynomial `X - C a`.
The actual normalization stalk at every endpoint branch is a DVR. Its Cartier
quotient length is the normalized additive valuation of that same equation.

The final original-fiber formula uses all normalization branches and the
residue degrees of the actual normalization morphism. No normality or
smoothness of the original curve, reducedness of its fiber, or choice of a
single branch is assumed. The generic affine scalar and DVR lemmas use
Mathlib structures. The normalization and cycle adapters still depend on the
existing Motivic finite-curve and integral-cycle modules.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped Polynomial BigOperators

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

variable {k : Type u} [Field k]
  (A : Type u) [CommRing A] [Algebra k[X] A]

/-- The actual affine endpoint scalar is the image of the original `X - C a`
under the structural algebra map and the actual stalk localization map. -/
theorem scalar_specMap (a : k) (p : Spec (.of A)) :
    scalar (Spec.map (CommRingCat.ofHom (algebraMap k[X] A))) a p =
      StructureSheaf.toStalk A p (algebraMap k[X] A (Polynomial.X - Polynomial.C a)) := by
  exact stalkMap_toStalk_apply (CommRingCat.ofHom (algebraMap k[X] A)) p
    (Polynomial.X - Polynomial.C a)

local instance affineStalkAlgebra (p : Spec (.of A)) :
    Algebra A ((Spec (.of A)).presheaf.stalk p) :=
  (StructureSheaf.toStalk A p).hom.toAlgebra

local instance affineStalkLocalization (p : Spec (.of A)) :
    IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk p) p.asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk p) p.asIdeal)

variable [FaithfulSMul k[X] A]

/-- A faithful affine-line parameter remains nonzero in every actual stalk. -/
theorem scalar_specMap_ne_zero [IsDomain A] (a : k) (p : Spec (.of A)) :
    scalar (Spec.map (CommRingCat.ofHom (algebraMap k[X] A))) a p ≠ 0 := by
  rw [scalar_specMap]
  exact (map_ne_zero_iff (StructureSheaf.toStalk A p).hom
    (IsLocalization.injective ((Spec (.of A)).presheaf.stalk p)
      p.asIdeal.primeCompl_le_nonZeroDivisors)).mpr
        ((FaithfulSMul.algebraMap_eq_zero_iff k[X] A).not.mpr (Polynomial.X_sub_C_ne_zero a))

/-- At an endpoint the actual prime is nonzero, even if the original fiber is
nonreduced. The witness is the unchanged structural parameter. -/
theorem endpoint_prime_ne_bot (a : k) (p : Spec (.of A))
    (hp : scalar (Spec.map (CommRingCat.ofHom (algebraMap k[X] A))) a p ∈
      IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk p)) :
    p.asIdeal ≠ ⊥ := by
  rw [scalar_specMap] at hp
  apply p.asIdeal.ne_bot_iff.mpr
  refine ⟨algebraMap k[X] A (Polynomial.X - Polynomial.C a), ?_, ?_⟩
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      ((Spec (.of A)).presheaf.stalk p) p.asIdeal _).mp hp
  · exact (FaithfulSMul.algebraMap_eq_zero_iff k[X] A).not.mpr
      (Polynomial.X_sub_C_ne_zero a)

/-- The actual endpoint stalk of a Dedekind finite-parameter curve is a DVR;
nonzero-primality is proved from the original endpoint equation. -/
theorem endpoint_stalk_isDiscreteValuationRing [IsDedekindDomain A]
    (a : k) (p : Spec (.of A))
    (hp : scalar (Spec.map (CommRingCat.ofHom (algebraMap k[X] A))) a p ∈
      IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk p)) :
    IsDiscreteValuationRing ((Spec (.of A)).presheaf.stalk p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A
    (endpoint_prime_ne_bot A a p hp) _

end AlgebraicGeometry.FiniteFlatCurve

namespace Motivic.FiniteCurveNormalization

open AlgebraicGeometry.FiniteFlatCurve

variable {k : Type u} [Field k] [CharZero k]
  (B : Type u) [CommRing B] [IsDomain B]
  [Algebra k[X] B] [Module.Finite k[X] B] [FaithfulSMul k[X] B]

omit [CharZero k] [Module.Finite k[X] B] in
/-- The normalization retains faithfulness over the original parameter ring. -/
theorem ring_faithfulSMul_base : FaithfulSMul k[X] (ring B) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq k[X] B (ring B)]
  exact (ring_algebraMap_injective B).comp (FaithfulSMul.algebraMap_injective k[X] B)

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] in
/-- The branch scalar is the image of the original target scalar through the
actual normalization stalk map, and lies in the actual branch maximal ideal. -/
theorem branch_scalar_mem_maximalIdeal (a : k) (y : fiber (baseMap (k := k) B) a)
    (x : {x : Spec (.of (ring B)) //
      normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y}) :
    scalar (normalizationMap B ≫ baseMap (k := k) B) a x.1 ∈
      IsLocalRing.maximalIdeal ((Spec (.of (ring B))).presheaf.stalk x.1) := by
  rw [← scalar_stalkMap]
  apply map_nonunit
  rw [x.2]
  exact scalar_mem_maximalIdeal (baseMap (k := k) B) a y

/-- Every actual normalization branch above the original endpoint has a DVR
stalk, derived from normalization rather than supplied as a hypothesis. -/
theorem branch_stalk_isDiscreteValuationRing (a : k)
    (y : fiber (baseMap (k := k) B) a)
    (x : {x : Spec (.of (ring B)) //
      normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y}) :
    IsDiscreteValuationRing ((Spec (.of (ring B))).presheaf.stalk x.1) := by
  let : FaithfulSMul k[X] (ring B) := ring_faithfulSMul_base B
  let : IsDedekindDomain (ring B) := ring_isDedekindDomain (k := k) B
  apply endpoint_stalk_isDiscreteValuationRing (ring B) a x.1
  rw [← normalizationMap_baseMap B]
  exact branch_scalar_mem_maximalIdeal B a y x

omit [CharZero k] [Module.Finite k[X] B] in
/-- The same original endpoint equation is nonzero in each normalization stalk. -/
theorem normalization_scalar_ne_zero (a : k) (x : Spec (.of (ring B))) :
    scalar (normalizationMap B ≫ baseMap (k := k) B) a x ≠ 0 := by
  let : FaithfulSMul k[X] (ring B) := ring_faithfulSMul_base B
  rw [normalizationMap_baseMap]
  exact scalar_specMap_ne_zero (ring B) a x

/-- The normalized additive valuation of the unchanged endpoint scalar in an
actual normalization branch. Its DVR structure is proved above. -/
def branchOrder (a : k) (y : fiber (baseMap (k := k) B) a)
    (x : {x : Spec (.of (ring B)) //
      normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y}) : ℕ∞ :=
  letI := branch_stalk_isDiscreteValuationRing B a y x
  IsDiscreteValuationRing.addVal ((Spec (.of (ring B))).presheaf.stalk x.1)
    (scalar (normalizationMap B ≫ baseMap (k := k) B) a x.1)

/-- Branch orders are finite before conversion to integer cycle coefficients. -/
theorem branchOrder_ne_top (a : k) (y : fiber (baseMap (k := k) B) a)
    (x : {x : Spec (.of (ring B)) //
      normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y}) :
    branchOrder B a y x ≠ ⊤ := by
  let := branch_stalk_isDiscreteValuationRing B a y x
  exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
    (normalization_scalar_ne_zero B a x.1)

/-- The full actual normalization Cartier quotient has its original scalar's
normalized DVR order as length, in ℕ∞ before any integer conversion. -/
theorem branch_cartierLength_eq_order (a : k) (y : fiber (baseMap (k := k) B) a)
    (x : {x : Spec (.of (ring B)) //
      normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y}) :
    Module.length ((Spec (.of (ring B))).presheaf.stalk x.1)
      (((Spec (.of (ring B))).presheaf.stalk x.1) ⧸
        Ideal.ofList [scalar (normalizationMap B ≫ baseMap (k := k) B) a x.1]) =
      branchOrder B a y x := by
  let := branch_stalk_isDiscreteValuationRing B a y x
  exact IsDiscreteValuationRing.length_quotient_ofList_eq_addVal _
    (normalization_scalar_ne_zero B a x.1)

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] in
/-- An actual normalized endpoint point determines its actual original fiber
point and normalization branch; no branch is chosen or discarded. -/
def normalizedPointBranch (a : k)
    (z : fiber (normalizationMap B ≫ baseMap (k := k) B) a) :
    {x : Spec (.of (ring B)) // normalizationMap B x =
      fiberInclusion (baseMap (k := k) B) a
        (fiberMap (baseMap (k := k) B) a (normalizationMap B) z)} :=
  ⟨fiberInclusion (normalizationMap B ≫ baseMap (k := k) B) a z,
    (congrArg (fun g => g z)
      (fiberMap_inclusion (baseMap (k := k) B) a (normalizationMap B))).symm⟩

/-- Each actual normalized endpoint coefficient is its normalized DVR order,
with all scheme-theoretic multiplicities preserved. -/
theorem normalization_fiber_fundamentalCoefficient_eq_order (a : k)
    (z : fiber (normalizationMap B ≫ baseMap (k := k) B) a) :
    letI : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
    letI : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
    letI : IsNoetherian (Spec (.of (ring B))) :=
      isNoetherian_of_finiteType (normalizationMap B)
    IntegralCycle.toPoints
        (fundamentalCycle (fiber (normalizationMap B ≫ baseMap (k := k) B) a)) z =
      ((branchOrder B a (fiberMap (baseMap (k := k) B) a (normalizationMap B) z)
        (normalizedPointBranch B a z)).toNat : ℤ) := by
  let : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
  let : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
  let : IsNoetherian (Spec (.of (ring B))) :=
    isNoetherian_of_finiteType (normalizationMap B)
  rw [fiber_fundamentalCoefficient]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (branch_cartierLength_eq_order B a _ (normalizedPointBranch B a z))

/-- The original, possibly singular endpoint coefficient is the sum over all
actual normalization branches, weighted by the actual residue-field degrees
and the normalized orders of the unchanged parameter. -/
theorem fiber_fundamentalCoefficient_eq_sum_branchOrders
    (a : k) (y : fiber (baseMap (k := k) B) a) :
    letI : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
    IntegralCycle.toPoints (fundamentalCycle (fiber (baseMap (k := k) B) a)) y =
      ∑ᶠ x : {x : Spec (.of (ring B)) //
        normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y},
        ((normalizationMap B).residueDegree x.1 : ℤ) * (branchOrder B a y x).toNat := by
  let : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
  let : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
  let : IsNoetherian (Spec (.of (ring B))) :=
    isNoetherian_of_finiteType (normalizationMap B)
  rw [← finitePushforward_fiber B a, fiberMap_fundamentalCoefficient]
  apply finsum_congr
  intro x
  rw [branch_cartierLength_eq_order]

/-- The original local quotient length has the same entire branch sum. The
original endpoint need not have length one or be reduced. -/
theorem cartierLength_eq_sum_branchOrders
    (a : k) (y : fiber (baseMap (k := k) B) a) :
    ((Module.length ((Spec (.of B)).presheaf.stalk
        (fiberInclusion (baseMap (k := k) B) a y))
      (((Spec (.of B)).presheaf.stalk (fiberInclusion (baseMap (k := k) B) a y)) ⧸
        Ideal.ofList [scalar (baseMap (k := k) B) a
          (fiberInclusion (baseMap (k := k) B) a y)])).toNat : ℤ) =
      ∑ᶠ x : {x : Spec (.of (ring B)) //
        normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y},
        ((normalizationMap B).residueDegree x.1 : ℤ) * (branchOrder B a y x).toNat := by
  let : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
  rw [← fiber_fundamentalCoefficient]
  exact fiber_fundamentalCoefficient_eq_sum_branchOrders B a y

end Motivic.FiniteCurveNormalization
