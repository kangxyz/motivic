/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.RelativeFiniteFlatSpan
public import MotivicTest.RelativeEndpointGeneratorComposition
public import MotivicTest.FiniteFlatSpanForgottenEndpoints

/-!
# Actual whole relative endpoints, including a nonfinite forgetting map

The source is the actual disjoint union of two affine lines, and the relative
family itself is proved nonreduced by its literal retraction. The retained
root gives a proved joint closed map. Forgetting that root is genuinely
nonfinite and merges its target images, while the exact endpoint source and
all multiplicities remain unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open MotivicTest.FlatPolynomialComponentRegularity
open MotivicTest.RelativeEndpointStalkTor MotivicTest.FiniteFlatSpanForgottenEndpoints

namespace MotivicTest.RelativeFiniteFlatSpanEndpoints
open _root_.AlgebraicGeometry.Scheme.SmoothSite

local instance : IsClosedImmersion
    (pullback.lift relativeDoubleProjection relativeRoot joint_base) :=
  inferInstanceAs (IsClosedImmersion joint)

/-- Literal relative endpoint graph precomposition on the whole original family. -/
theorem actual_retained_endpoint (a : ℚ) :
    (Cor.graphFunctor ℚ).map (endpointMorphism twoLines a) ≫
        Cor.ofFiniteFlatSpan (X := relativeLineSite twoLines)
          (Y := AffineLineField.line ℚ) relativeDoubleProjection relativeRoot joint_base =
      Cor.relativeFiniteFlatSpanEndpoint (X := twoLines) (Y := AffineLineField.line ℚ)
        relativeDoubleProjection relativeRoot joint_base a :=
  Cor.graph_relative_endpoint_ofFiniteFlatSpan relativeDoubleProjection relativeRoot joint_base a

/-- The original whole family and both whole endpoints survive unrestricted
forgetting of the root. No finiteness hypothesis on the forgetting map is used. -/
theorem actual_forgotten_endpoint (a : ℚ) :
    (Cor.graphFunctor ℚ).map (endpointMorphism twoLines a) ≫
        Cor.ofFiniteFlatSpan (X := relativeLineSite twoLines)
          (Y := AffineLineField.point ℚ) relativeDoubleProjection
          (relativeRoot ≫ (forgetRoot ℚ).left)
          (Cor.finiteFlatSpan_postcompose_base (X := relativeLineSite twoLines)
            relativeDoubleProjection relativeRoot joint_base (forgetRoot ℚ)) =
      Cor.relativeFiniteFlatSpanEndpoint (X := twoLines) (Y := AffineLineField.point ℚ)
        relativeDoubleProjection (relativeRoot ≫ (forgetRoot ℚ).left)
        (Cor.finiteFlatSpan_postcompose_base (X := relativeLineSite twoLines)
          relativeDoubleProjection relativeRoot joint_base (forgetRoot ℚ)) a :=
  Cor.graph_relative_endpoint_ofFiniteFlatSpan_postcompose
    relativeDoubleProjection relativeRoot joint_base (forgetRoot ℚ) a

example : ¬ IsFinite (forgetRoot ℚ).left := forgetRoot_not_finite ℚ

example : ¬ AlgebraicGeometry.IsReduced relativeDoubleFamily :=
  MotivicTest.RelativeFiniteFlatSpecialization.relativeDoubleFamily_not_reduced

example : ¬ PreconnectedSpace twoLines.left :=
  MotivicTest.RelativeEndpointIncidenceTor.twoLines_not_preconnected

example := actual_retained_endpoint 0

example := actual_retained_endpoint 1

example := actual_forgotten_endpoint 0

example := actual_forgotten_endpoint 1

open Lean in
run_cmd do
  for name in #[``actual_retained_endpoint, ``actual_forgotten_endpoint,
      ``Cor.graph_relative_endpoint_ofFiniteFlatSpan,
      ``Cor.graph_relative_endpoint_ofFiniteFlatSpan_postcompose] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"

end MotivicTest.RelativeFiniteFlatSpanEndpoints
