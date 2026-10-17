/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteCurvePushforwardSpecialization
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.FieldTheory.Perfect

/-!
# Normalization over the original finite curve parameter

For a finite faithful domain algebra over `k[X]` in characteristic zero, its
integral closure in its own fraction field is finite over the original base.
The canonical normalization map has generic residue degree one. Its finite
pushforward preserves the whole actual endpoint fundamental cycle, including
all branch and nonreduced multiplicities.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

universe u

namespace Motivic.FiniteCurveNormalization

/-- The actual integral closure in the original domain's own fraction field. -/
abbrev ring (B : Type u) [CommRing B] [IsDomain B] :=
  integralClosure B (FractionRing B)

variable (B : Type u) [CommRing B] [IsDomain B]

/-- Normalization has the original domain's literal fraction field. -/
instance ring_isFractionRing : IsFractionRing (ring B) (FractionRing B) :=
  integralClosure.isFractionRing_of_finite_extension (FractionRing B) (FractionRing B)

/-- The actual integral closure is integrally closed. -/
instance ring_isIntegrallyClosed : IsIntegrallyClosed (ring B) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (K := FractionRing B)

/-- The inclusion of the original domain in its normalization has rank one. -/
theorem ring_finrank : Module.finrank B (ring B) = 1 := by
  rw [← IsFractionRing.finrank_eq B (FractionRing B) (ring B) (FractionRing B)]
  exact Module.finrank_self _

/-- The normalization morphism is induced by the original domain inclusion. -/
def normalizationMap : Spec (.of (ring B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (ring B)))

/-- The original domain embeds in its actual integral closure. -/
theorem ring_algebraMap_injective : Function.Injective (algebraMap B (ring B)) := by
  intro x y h
  exact IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val h)

/-- The actual normalization morphism is surjective, by integral lying over. -/
instance normalizationMap_surjective : Surjective (normalizationMap B) := by
  let : FaithfulSMul B (ring B) :=
    (faithfulSMul_iff_algebraMap_injective B (ring B)).mpr (ring_algebraMap_injective B)
  exact ⟨Algebra.IsIntegral.comap_surjective B (ring B)⟩

/-- The actual generic residue scalar map has degree one, not merely an
unrelated isomorphism between the two abstract fields. -/
theorem normalizationMap_residueDegree [Module.Finite B (ring B)] :
    (normalizationMap B).residueDegree (genericPoint (Spec (.of (ring B)))) = 1 := by
  rw [genericPoint_eq_bot_of_affine]
  exact (GenericFinitePushforwardMultiplicity.finrank_eq_residueDegree
    (.of B) (.of (ring B)) (ring_algebraMap_injective B)).symm.trans (ring_finrank B)

section FiniteBase

variable {k : Type u} [Field k] [CharZero k]
  [Algebra k[X] B] [Module.Finite k[X] B] [FaithfulSMul k[X] B]

attribute [local instance] FractionRing.liftAlgebra

omit [CharZero k] in
/-- The actual finite domain algebra gives a finite extension of fraction fields. -/
theorem fractionRing_finite : Module.Finite (FractionRing k[X]) (FractionRing B) :=
  Module.Finite.of_isLocalization k[X] B (nonZeroDivisors k[X])

/-- Characteristic zero makes the derived finite fraction-field extension separable. -/
theorem fractionRing_separable : Algebra.IsSeparable (FractionRing k[X]) (FractionRing B) := by
  let : Module.Finite (FractionRing k[X]) (FractionRing B) := fractionRing_finite B
  infer_instance

omit [CharZero k] [FaithfulSMul k[X] B] in
/-- Transitivity identifies this same ring as the closure of the original base. -/
theorem ring_isIntegralClosure_base : IsIntegralClosure (ring B) k[X] (FractionRing B) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx.tower_top⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact isIntegral_trans (A := B) _ x.property

/-- The actual normalization is finite over the original polynomial base. -/
theorem ring_finite_base : Module.Finite k[X] (ring B) := by
  let : Module.Finite (FractionRing k[X]) (FractionRing B) := fractionRing_finite B
  let : Algebra.IsSeparable (FractionRing k[X]) (FractionRing B) := fractionRing_separable B
  let : IsIntegralClosure (ring B) k[X] (FractionRing B) := ring_isIntegralClosure_base B
  exact IsIntegralClosure.finite k[X] (FractionRing k[X]) (FractionRing B) (ring B)

include k in
/-- The constructed normalization is a Dedekind domain over the original base. -/
theorem ring_isDedekindDomain : IsDedekindDomain (ring B) := by
  let : Module.Finite (FractionRing k[X]) (FractionRing B) := fractionRing_finite B
  let : Algebra.IsSeparable (FractionRing k[X]) (FractionRing B) := fractionRing_separable B
  let : IsIntegralClosure (ring B) k[X] (FractionRing B) := ring_isIntegralClosure_base B
  exact IsIntegralClosure.isDedekindDomain k[X] (FractionRing k[X]) (FractionRing B) (ring B)

include k in
/-- Finiteness over the original base also makes the normalization finite
as a module over the original, possibly singular curve ring. -/
theorem ring_finite : Module.Finite B (ring B) := by
  let : Module.Finite k[X] (ring B) := ring_finite_base B
  exact Module.Finite.of_restrictScalars_finite k[X] B (ring B)

/-- The original structural morphism to the original polynomial parameter. -/
def baseMap : Spec (.of B) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] B))

omit [CharZero k] [FaithfulSMul k[X] B] in
/-- The original structural morphism is finite by the supplied finite algebra. -/
instance baseMap_isFinite : IsFinite (baseMap (k := k) B) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

omit [CharZero k] in
/-- The original structural morphism is surjective by integral lying over. -/
instance baseMap_surjective : Surjective (baseMap (k := k) B) :=
  ⟨Algebra.IsIntegral.comap_surjective k[X] B⟩

include k in
/-- The actual normalization map is finite, with no extra normalization hypothesis. -/
theorem normalizationMap_isFinite : IsFinite (normalizationMap B) := by
  let : Module.Finite B (ring B) := ring_finite (k := k) B
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] in
/-- The normalization is over the original parameter map, without changing coordinates. -/
theorem normalizationMap_baseMap :
    normalizationMap B ≫ baseMap (k := k) B =
      Spec.map (CommRingCat.ofHom (algebraMap k[X] (ring B))) := by
  rw [normalizationMap, baseMap, ← Spec.map_comp]
  congr 1

open AlgebraicGeometry.FiniteFlatCurve in
/-- The whole actual endpoint fundamental cycle is unchanged under normalization
pushforward. This retains every branch and every original Cartier length. -/
theorem finitePushforward_fiber (a : k) :
    letI : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
    letI : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
    letI : IsNoetherian (Spec (.of (ring B))) :=
      isNoetherian_of_finiteType (normalizationMap B)
    IntegralCycle.finitePushforward (fiberMap (baseMap (k := k) B) a (normalizationMap B))
        (fundamentalCycle (fiber (normalizationMap B ≫ baseMap (k := k) B) a)) =
      fundamentalCycle (fiber (baseMap (k := k) B) a) := by
  let : Module.Finite B (ring B) := ring_finite (k := k) B
  let : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
  let : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
  let : IsNoetherian (Spec (.of (ring B))) :=
    isNoetherian_of_finiteType (normalizationMap B)
  simpa only [normalizationMap_residueDegree, Nat.cast_one, one_zsmul] using
    AlgebraicGeometry.finiteCurve_finitePushforward_fiber
      (baseMap (k := k) B) (normalizationMap B) a

end FiniteBase

end Motivic.FiniteCurveNormalization
