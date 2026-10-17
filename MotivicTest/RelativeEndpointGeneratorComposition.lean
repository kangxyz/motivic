/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointGeneratorComposition
public import MotivicTest.RelativeFiniteFlatSpecialization

/-!
# Whole relative generator endpoint consumers

On the actual two-component positive-dimensional source, an arbitrary right
generator selects a unique source component. Graph precomposition is then the
full original endpoint pullback fundamental cycle. No support-flatness input
is present. The genuinely nonreduced relative-family consumer is also retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.RelativeEndpointDiagram MotivicTest.FlatPolynomialComponentRegularity

namespace MotivicTest.RelativeEndpointGeneratorComposition

local instance : IsNoetherian ((𝟭 Scheme).obj twoLines.left) :=
  inferInstanceAs (IsNoetherian twoLines.left)

variable (G : FiniteCorrespondenceGenerator
  (relativeLineHom twoLines.hom) (FiniteFlatCurveFamily.line ℚ).hom)

/-- A genuine arbitrary integral support chooses exactly one of the source components. -/
theorem actual_unique_component :
    ∃! C : Set twoLines.left, C ∈ irreducibleComponents twoLines.left ∧
      Set.range (G.projection ≫ pullback.fst twoLines.hom
        (FiniteFlatCurveFamily.line ℚ).hom) ⊆ C :=
  G.existsUnique_sourceComponent_of_integral (X := twoLines)
    (Y := relativeLineSite twoLines) (Z := FiniteFlatCurveFamily.line ℚ)
    (pullback.fst twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom)

/-- The actual categorical graph restriction retains the whole original support fiber. -/
theorem actual_generator_endpoint (a : ℚ) :
    FiniteCorrespondence.toIntegralCycle (f := twoLines.hom)
      (g := (FiniteFlatCurveFamily.line ℚ).hom)
      ((Cor.graphFunctor ℚ).map (endpointMorphism twoLines a) ≫
        (show Cor.mk (relativeLineSite twoLines) ⟶ Cor.mk (FiniteFlatCurveFamily.line ℚ)
          from G.cycle)) =
      IntegralCycle.finitePushforward
        (G.graphPullbackMap (endpoint twoLines.hom a) (endpoint_base twoLines.hom a))
        (fundamentalCycle (G.graphPullback (endpoint twoLines.hom a))) :=
  toIntegralCycle_graph_endpoint_generator twoLines (FiniteFlatCurveFamily.line ℚ) a G

example : ¬ AlgebraicGeometry.IsReduced relativeDoubleFamily :=
  MotivicTest.RelativeFiniteFlatSpecialization.relativeDoubleFamily_not_reduced

example : ¬ PreconnectedSpace twoLines.left :=
  MotivicTest.RelativeEndpointIncidenceTor.twoLines_not_preconnected

example := actual_generator_endpoint G 0

example := actual_generator_endpoint G 1

open Lean in
run_cmd do
  for name in #[``actual_unique_component, ``actual_generator_endpoint,
      ``FiniteCorrespondenceGenerator.componentGraphPullbackMap_isIso,
      ``FiniteCorrespondenceGenerator.componentGraph_incidence_isEmpty_of_ne] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"

end MotivicTest.RelativeEndpointGeneratorComposition
