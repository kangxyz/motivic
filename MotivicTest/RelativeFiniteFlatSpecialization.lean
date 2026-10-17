/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeFiniteFlatSpecialization
public import MotivicTest.RelativeEndpointIncidenceTor

/-!
# Whole relative endpoint specialization consumers

The relative base is the actual disjoint union of two affine lines. The whole
family is the base change of the two-double-section monic quotient. A literal
retraction proves that the relative family itself is nonreduced. Both endpoint
cycle formulas use its whole original pullbacks and original generic weights.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteTwoUnitPolynomialFamily
open Motivic.RelativeEndpointDiagram MotivicTest.FlatPolynomialComponentRegularity
open MotivicTest.FiniteFlatSpanEndpoints
open scoped BigOperators

namespace MotivicTest.RelativeFiniteFlatSpecialization

/-- A rational point in the first of the two actual source components. -/
def sourcePoint : FiniteFlatCurveFamily.point ℚ ⟶ twoLines :=
  FiniteFlatCurveFamily.evaluationPoint ℚ 0 ≫
    SmoothSite.coproductInl (FiniteFlatCurveFamily.line ℚ) (FiniteFlatCurveFamily.line ℚ)

/-- The literal parameter projection has a section supplied by that source point. -/
def parameterSection : (FiniteFlatCurveFamily.line ℚ).left ⟶ relativeBase twoLines :=
  pullback.lift ((FiniteFlatCurveFamily.line ℚ).hom ≫ sourcePoint.left) (𝟙 _) (by
    rw [Category.assoc, MorphismProperty.Over.w]
    change (FiniteFlatCurveFamily.line ℚ).hom ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp)

@[reassoc (attr := simp)]
theorem parameterSection_snd : parameterSection ≫ parameter twoLines = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The whole original nonreduced family is a retract of its relative base change. -/
def familySection : familyScheme twoDoubleSections ⟶ relativeDoubleFamily :=
  pullback.lift (𝟙 _) (projection twoDoubleSections ≫ parameterSection) (by
    rw [Category.id_comp, Category.assoc, parameterSection_snd]
    exact (Category.comp_id _).symm)

@[reassoc (attr := simp)]
theorem familySection_fst : familySection ≫
    pullback.fst (projection twoDoubleSections) (parameter twoLines) = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- Nonreducedness is proved for the relative family itself, not only its ancestor. -/
theorem relativeDoubleFamily_not_reduced : ¬ AlgebraicGeometry.IsReduced relativeDoubleFamily := by
  intro h
  have := h
  let r := pullback.fst (projection twoDoubleSections) (parameter twoLines)
  have hi : Function.Injective r.appTop := by
    apply Function.LeftInverse.injective (g := familySection.appTop)
    intro q
    change (r.appTop ≫ familySection.appTop) q = q
    rw [← Scheme.Hom.comp_appTop]
    change (familySection ≫
      pullback.fst (projection twoDoubleSections) (parameter twoLines)).appTop q = q
    rw [familySection_fst]
    rfl
  have : _root_.IsReduced Γ(familyScheme twoDoubleSections, ⊤) :=
    isReduced_of_injective r.appTop.hom hi
  have : AlgebraicGeometry.IsReduced (familyScheme twoDoubleSections) :=
    isReduced_of_isAffine_isReduced _
  exact twoDoubleSections_not_reduced
    ((affine_isReduced_iff (.of (AdjoinRoot twoDoubleSections))).mp this)

/-- The exact component fiber map preserves generic support in the whole endpoint. -/
theorem actual_component_generics (a : ℚ) (z : genericPoints relativeDoubleFamily)
    (w : FiniteFlatCurve.fiber (RelativeFiniteFlat.componentInclusion z ≫
      familyParameter twoLines.hom relativeDoubleProjection) a)
    (hw : w ∈ genericPoints (FiniteFlatCurve.fiber (RelativeFiniteFlat.componentInclusion z ≫
      familyParameter twoLines.hom relativeDoubleProjection) a)) :
    FiniteFlatCurve.fiberMap (familyParameter twoLines.hom relativeDoubleProjection) a
      (RelativeFiniteFlat.componentInclusion z) w ∈
        genericPoints (FiniteFlatCurve.fiber
          (familyParameter twoLines.hom relativeDoubleProjection) a) :=
  componentFiberMap_mem_genericPoints_smooth twoLines relativeDoubleProjection a z w hw

local instance (a : ℚ) :
    IsNoetherian (pullback (endpoint twoLines.hom a) relativeDoubleProjection) :=
  haveI : IsNoetherian ((𝟭 Scheme).obj twoLines.left) :=
    inferInstanceAs (IsNoetherian twoLines.left)
  isNoetherian_of_finiteType (pullback.fst (endpoint twoLines.hom a) relativeDoubleProjection)

local instance (a : ℚ) (z : genericPoints relativeDoubleFamily) :
    IsNoetherian (pullback (endpoint twoLines.hom a)
      (RelativeFiniteFlat.componentInclusion z ≫ relativeDoubleProjection)) :=
  haveI : IsNoetherian ((𝟭 Scheme).obj twoLines.left) :=
    inferInstanceAs (IsNoetherian twoLines.left)
  isNoetherian_of_finiteType (pullback.fst (endpoint twoLines.hom a)
    (RelativeFiniteFlat.componentInclusion z ≫ relativeDoubleProjection))

/-- The whole original relative pullback satisfies the weighted component formula. -/
theorem actual_whole_endpoint (a : ℚ) :
    let : IsNoetherian relativeDoubleFamily :=
      relativeFiniteFlat_isNoetherian twoLines relativeDoubleProjection
    let := IntegralCycle.genericPointFintype relativeDoubleFamily
    fundamentalCycle (pullback (endpoint twoLines.hom a) relativeDoubleProjection) =
      ∑ z : genericPoints relativeDoubleFamily, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (RelativeFiniteFlat.componentBaseChangeMap relativeDoubleProjection
            (endpoint twoLines.hom a) z)
          (fundamentalCycle (pullback (endpoint twoLines.hom a)
            (RelativeFiniteFlat.componentInclusion z ≫ relativeDoubleProjection))) :=
  relativeFiniteFlat_fundamentalCycle_specialization twoLines relativeDoubleProjection a

example : ¬ PreconnectedSpace twoLines.left :=
  MotivicTest.RelativeEndpointIncidenceTor.twoLines_not_preconnected

example := actual_whole_endpoint 0

example := actual_whole_endpoint 1

open Lean in
run_cmd do
  for name in #[``relativeDoubleFamily_not_reduced, ``actual_component_generics,
      ``actual_whole_endpoint,
      ``AlgebraicGeometry.RelativeFiniteFlat.componentBaseChangeMap_mem_genericPoints,
      ``AlgebraicGeometry.relativeFiniteFlat_fundamentalCycle_specialization] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"

end MotivicTest.RelativeFiniteFlatSpecialization
