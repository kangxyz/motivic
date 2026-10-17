/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalFinitePointEvaluation
public import Lean.Util.CollectAxioms

/-! Consumers of whole finite-point evaluation and actual identity-axis relations. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.DiagonalCycleSymbols Motivic.DiagonalPointNorm
open Motivic.DiagonalFinitePointEvaluation Motivic.KTheory.MilnorK

universe u

namespace MotivicTest.DiagonalFinitePointEvaluation

variable (k E : Type u) [Field k] [CharZero k] [Field E]
  [Algebra k E] [Module.Finite k E]

/-- A proper image subfield still contributes the full norm from the given field. -/
theorem actual_entire_finite_point (q : ℕ) (j : Spec (.of E) ⟶ ambient k q) [IsFinite j]
    (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k E))) :
    cycleValue k q (finitePointCorrespondence j hj) =
      finiteExtensionNorm k E q (symbol (affineCoordinateUnit j)) :=
  cycleValue_finitePointCorrespondence j hj

/-- The actual axis relation, not just rational axis graphs, is killed. -/
theorem actual_full_axis (q : ℕ) (i : Fin (q + 1))
    (α : WeightOnePointNorm.point k ⟶ target k q) :
    cycleValue k (q + 1) (α ≫ (Cor.graphFunctor k).map
      (SmoothSite.torusInsertOne (.of k) q i)) = 0 := cycleValue_axis i α

open Lean in
run_cmd do
  for name in #[``imageGenerator, ``finitePointCorrespondence,
      ``toIntegralCycle_finitePointCorrespondence, ``imageScalarMap,
      ``imageScalarMap_comp, ``imageScalarMap_coordinate,
      ``residueDegree_eq_image_finrank, ``norm_symbol_map_degree,
      ``cycleValue_finitePointCorrespondence, ``cycleValue_eq_norm_of_finite_fundamental,
      ``cycleValue_eq_norm_units_of_finite_fundamental,
      ``cycleValue_cycle_comp_graph, ``affineCoordinateUnit_axis,
      ``cycleValue_cycle_axis, ``cycleValue_axis,
      ``actual_entire_finite_point, ``actual_full_axis] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole finite-point evaluation and identity axes use only standard foundations."

end MotivicTest.DiagonalFinitePointEvaluation
