/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneFundamentalNorm
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual finite fundamental-cycle norm

The tests retain arbitrary finite algebras, every maximal quotient, the
original scheme stalk lengths, and the genuine correspondence cycle norm.
No reducedness, separability, or integral-whole-fiber assumption is present.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.WeightOnePointNorm Motivic.WeightOneFundamentalNorm

universe u

namespace MotivicTest.WeightOneFundamentalNorm

variable {k : Type u} [Field k]

/-- All maximal branches carry the lengths of the original, possibly
nonreduced scheme stalks. -/
theorem original_stalk_multiplicity
    {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R]
    (q : MaximalSpectrum R) :
    genericMultiplicity ⟨q.toPrimeSpectrum, finiteAlgebra_mem_genericPoints (k := k) _⟩ =
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat :=
  affine_genericMultiplicity (k := k) q

/-- These local lengths are genuinely finite before conversion to naturals. -/
theorem original_local_length_finite
    {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R]
    (q : MaximalSpectrum R) :
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) ≠ ⊤ :=
  Algebra.local_length_ne_top_of_finite (k := k) q

/-- The actual assembled correspondence has the determinant norm of the
whole algebra, without discarding nilpotents or disconnected branches. -/
theorem entire_finite_algebra_norm
    {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R]
    (j : Spec (.of R) ⟶ ambient k) [IsClosedImmersion j]
    (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    cycleNorm k (affineFundamentalCorrespondence j hj) =
      Additive.ofMul (Units.map (Algebra.norm k) (affineCoordinateUnit j)) :=
  cycleNorm_affineFundamentalCorrespondence j hj

/-- The adapter applies to an arbitrary literal finite scheme whose full
fundamental pushforward is the given actual correspondence. -/
theorem entire_finite_scheme_norm
    {T : Scheme.{u}} [IsNoetherian T]
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k) [IsClosedImmersion j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom = p)
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    cycleNorm k α = Additive.ofMul (schemeNorm p j) :=
  cycleNorm_eq_norm_of_fundamental p j hp α hα

/-- Arbitrary signed multiples retain their actual multiplicities. -/
theorem signed_finite_scheme_norm
    {T : Scheme.{u}} [IsNoetherian T]
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k) [IsClosedImmersion j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom = p)
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) (n : ℤ) :
    cycleNorm k (n • α) = n • Additive.ofMul (schemeNorm p j) := by
  rw [map_zsmul, cycleNorm_eq_norm_of_fundamental p j hp α hα]

end MotivicTest.WeightOneFundamentalNorm

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightOneFundamentalNorm.fieldGenerator,
      `Motivic.WeightOneFundamentalNorm.fieldCoordinateEquiv,
      `Motivic.WeightOneFundamentalNorm.fieldCoordinateEquiv_coordinate,
      `Motivic.WeightOneFundamentalNorm.generatorNorm_fieldGenerator,
      `Motivic.WeightOneFundamentalNorm.quotientMap_genericPoint,
      `Motivic.WeightOneFundamentalNorm.quotientSupport_point,
      `Motivic.WeightOneFundamentalNorm.finiteAlgebra_mem_genericPoints,
      `Motivic.WeightOneFundamentalNorm.affine_genericMultiplicity,
      `Motivic.WeightOneFundamentalNorm.fundamentalCycle_affine_eq_sum,
      `Motivic.WeightOneFundamentalNorm.branchGenerator_support,
      `Motivic.WeightOneFundamentalNorm.affineCoordinateUnit_quotient,
      `Motivic.WeightOneFundamentalNorm.affineFundamentalCorrespondence,
      `Motivic.WeightOneFundamentalNorm.toIntegralCycle_affineFundamentalCorrespondence,
      `Motivic.WeightOneFundamentalNorm.cycleNorm_affineFundamentalCorrespondence,
      `Motivic.WeightOneFundamentalNorm.cycleNorm_eq_norm_of_affine_fundamental,
      `Motivic.WeightOneFundamentalNorm.schemeScalarMap,
      `Motivic.WeightOneFundamentalNorm.schemeCoordinateUnit,
      `Motivic.WeightOneFundamentalNorm.schemeNorm,
      `Motivic.WeightOneFundamentalNorm.affineCoordinateUnit_isoSpec,
      `Motivic.WeightOneFundamentalNorm.cycleNorm_eq_norm_of_fundamental,
      `MotivicTest.WeightOneFundamentalNorm.original_stalk_multiplicity,
      `MotivicTest.WeightOneFundamentalNorm.original_local_length_finite,
      `MotivicTest.WeightOneFundamentalNorm.entire_finite_algebra_norm,
      `MotivicTest.WeightOneFundamentalNorm.entire_finite_scheme_norm,
      `MotivicTest.WeightOneFundamentalNorm.signed_finite_scheme_norm] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite fundamental-cycle norms use only standard Lean foundations."
