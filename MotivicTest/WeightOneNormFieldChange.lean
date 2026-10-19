/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.NormFieldChange
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual arbitrary-field-change point norms

These consumers keep the original signed correspondences, whole fundamental
supports, and reduced-torus quotient maps, over arbitrary field homomorphisms.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (IntegralCycle)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic
open Motivic.WeightOnePointNorm
open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.Motivic.WeightOneFundamentalNorm
open Motivic.WeightOneNormFieldChange _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.WeightOneNormFieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- There is no finite, separable, or finite-type assumption on the field map. -/
theorem all_signed_point_cycles (α : point k ⟶ target k) :
    cycleNorm L (baseTorusCycleFieldChange φ 1 α) =
      Additive.ofMul (Units.map φ.toMonoidHom (cycleNorm k α).toMul) :=
  cycleNorm_baseTorusCycleFieldChange φ α

/-- The actual functor, conjugated by its literal base/torus comparisons,
retains every component and the lengths of the original whole pulled support. -/
theorem whole_fundamental_support (A : Generator k) :
    FiniteCorrespondence.toIntegralCycle (f := (SmoothSite.base (Spec (.of L))).hom)
      (g := (SmoothSite.torusPower (.of L) 1).hom)
      (baseTorusCycleFieldChange φ 1 A.cycle) =
      IntegralCycle.finitePushforward (fieldChangeInclusion φ A)
        (fundamentalCycle (A.fieldBaseChangeSupport φ)) :=
  toIntegralCycle_baseTorusCycleFieldChange_cycle φ A

/-- Negative and positive multiplicities use the same actual cycle map. -/
theorem signed_multiplicity (A : Generator k) (n : ℤ) :
    cycleNorm L (baseTorusCycleFieldChange φ 1 (Finsupp.single A n)) =
      n • Additive.ofMul (Units.map φ.toMonoidHom (generatorNorm A)) := by
  rw [cycleNorm_baseTorusCycleFieldChange, cycleNorm_single, map_zsmul]
  rfl

/-- The norm square commutes on all actual reduced quotient sections. -/
theorem actual_reduced_norm_square
    (s : sections (reducedTorus k 1) (point k)) :
    reducedNorm L (baseReducedTorusFieldChange φ 1 s) =
      Additive.ofMul (Units.map φ.toMonoidHom (reducedNorm k s).toMul) :=
  reducedNorm_baseReducedTorusFieldChange φ s

/-- Rational units retain the original orientation under arbitrary field change. -/
theorem actual_unit_graph (a : kˣ) :
    cycleNorm L (baseTorusCycleFieldChange φ 1
      ((Cor.graphFunctor k).map (rationalPoint k a))) =
      Additive.ofMul (Units.map φ.toMonoidHom a) := by
  exact (cycleNorm_baseTorusCycleFieldChange φ
    ((Cor.graphFunctor k).map (rationalPoint k a))).trans
      (congrArg (unitsFieldChange φ) (cycleNorm_graph_unit a))

end MotivicTest.WeightOneNormFieldChange

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightOneNormFieldChange.toIntegralCycle_comp_graphIso,
      `Motivic.WeightOneNormFieldChange.toIntegralCycle_graphIso_comp,
      `Motivic.WeightOneNormFieldChange.ambientFieldChangeIso,
      `Motivic.WeightOneNormFieldChange.fieldChangeInclusion,
      `Motivic.WeightOneNormFieldChange.fieldChangeInclusion_fst,
      `Motivic.WeightOneNormFieldChange.fieldChangeInclusion_snd,
      `Motivic.WeightOneNormFieldChange.fieldChangeInclusion_coordinate,
      `Motivic.WeightOneNormFieldChange.fieldChangeInclusion_coordinateUnit,
      `Motivic.WeightOneNormFieldChange.schemeNorm_fieldChangeInclusion,
      `Motivic.WeightOneNormFieldChange.unitsFieldChange,
      `Motivic.WeightOneNormFieldChange.toIntegralCycle_conjugated_fieldBaseChange_cycle,
      `Motivic.WeightOneNormFieldChange.cycleNorm_conjugated_fieldBaseChange_cycle,
      `Motivic.WeightOneNormFieldChange.cycleNorm_conjugated_fieldBaseChange,
      `Motivic.WeightOneNormFieldChange.toIntegralCycle_baseTorusCycleFieldChange_cycle,
      `Motivic.WeightOneNormFieldChange.cycleNorm_baseTorusCycleFieldChange_cycle,
      `Motivic.WeightOneNormFieldChange.cycleNorm_baseTorusCycleFieldChange,
      `Motivic.WeightOneNormFieldChange.reducedNorm_baseReducedTorusFieldChange,
      `MotivicTest.WeightOneNormFieldChange.all_signed_point_cycles,
      `MotivicTest.WeightOneNormFieldChange.whole_fundamental_support,
      `MotivicTest.WeightOneNormFieldChange.signed_multiplicity,
      `MotivicTest.WeightOneNormFieldChange.actual_reduced_norm_square,
      `MotivicTest.WeightOneNormFieldChange.actual_unit_graph] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual arbitrary-field-change point norms use only standard Lean foundations."
