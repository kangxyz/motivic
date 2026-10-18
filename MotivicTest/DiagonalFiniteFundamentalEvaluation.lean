/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalFiniteFundamentalEvaluation
public import Lean.Util.CollectAxioms

/-! Whole finite fibers, including local lengths and proper-image residue degrees. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.DiagonalCycleSymbols Motivic.DiagonalPointNorm
open Motivic.DiagonalFinitePointEvaluation Motivic.DiagonalFiniteFundamentalEvaluation
open MilnorK
open scoped BigOperators

universe u

namespace MotivicTest.DiagonalFiniteFundamentalEvaluation

variable (k : Type u) [Field k] [CharZero k]

/-- This consumer requires no reducedness or immersion of the whole algebra. -/
theorem actual_whole_affine_finite_cycle (q : ℕ)
    (R : Type u) [CommRing R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ ambient k q) [IsFinite j]
    (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    FiniteCorrespondence.toIntegralCycle (affineFundamentalCorrespondence j hj) =
        IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R))) ∧
      cycleValue k q (affineFundamentalCorrespondence j hj) =
        affineFundamentalValue (k := k) (affineCoordinateUnit j) :=
  ⟨toIntegralCycle_affineFundamentalCorrespondence j hj,
    cycleValue_affineFundamentalCorrespondence j hj⟩

/-- The finite normalization endpoint may have several nonreduced branches. -/
theorem actual_whole_finite_scheme (q : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k q) [IsFinite j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom = p)
    (a : Fin q → Γ(T, ⊤)ˣ) (ha : ∀ i, schemeCoordinateUnit j i = a i)
    (α : WeightOnePointNorm.point k ⟶ target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    cycleValue k q α = schemeFundamentalValue p a :=
  cycleValue_eq_norms_units_of_fundamental p j hp a ha α hα

open Lean in
run_cmd do
  for name in #[``localMultiplicity, ``branch_projection,
      ``affineCoordinateUnit_quotient, ``affineFundamentalCorrespondence,
      ``finitePushforward_quotient_fundamental,
      ``toIntegralCycle_affineFundamentalCorrespondence,
      ``affineFundamentalValue, ``cycleValue_affineFundamentalCorrespondence,
      ``cycleValue_eq_norms_of_affine_fundamental,
      ``cycleValue_eq_norms_units_of_affine_fundamental,
      ``schemeCoordinateUnit, ``affineCoordinateUnit_isoSpec,
      ``schemeScalarMap_finite, ``schemeFundamentalValue,
      ``cycleValue_eq_norms_of_fundamental,
      ``cycleValue_eq_norms_units_of_fundamental,
      ``actual_whole_affine_finite_cycle, ``actual_whole_finite_scheme] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole finite fundamental evaluation uses only standard foundations."

end MotivicTest.DiagonalFiniteFundamentalEvaluation
