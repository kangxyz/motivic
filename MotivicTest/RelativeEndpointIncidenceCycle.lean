/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Relative.IncidenceCycle
public import MotivicTest.RelativeEndpointIncidenceTor

/-!
# Actual component endpoint fundamental-correspondence consumers

The two-line source is genuinely disconnected. The original component incidence
Tor coefficient is its whole generic local length, and the actual correspondence
is finite pushforward of the full incidence fundamental cycle. No right-support
flatness or reduction of the incidence is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (IntegralCycle fundamentalCycle genericMultiplicity)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open MotivicTest.FlatPolynomialComponentRegularity

namespace MotivicTest.RelativeEndpointIncidenceCycle
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

variable (a : ℚ) (E : Set twoLines.left) (hE : E ∈ irreducibleComponents twoLines.left)
  (G : FiniteCorrespondenceGenerator (relativeLineHom twoLines.hom)
    (AffineLineField.line ℚ).hom)

local instance : IsNoetherian ((endpointComponentGenerator twoLines a E hE).incidence G) :=
  FiniteCorrespondenceGenerator.isNoetherian_smoothIncidence ℚ
    (X := twoLines) (Y := relativeLineSite twoLines) (Z := AffineLineField.line ℚ)
    (endpointComponentGenerator twoLines a E hE) G

/-- The actual Euler coefficient retains the full original generic incidence length. -/
theorem actual_component_coefficient
    (x : genericPoints ((endpointComponentGenerator twoLines a E hE).incidence G)) :
    (endpointComponentGenerator twoLines a E hE).incidenceTorCoefficient (S := Spec (.of ℚ)) G x =
      (genericMultiplicity x : ℤ) :=
  component_incidenceTorCoefficient_eq_genericMultiplicity
    twoLines (AffineLineField.line ℚ) a E hE G x

/-- The correspondence itself retains the whole fundamental incidence, not only
an equality between auxiliary numerical weights. -/
theorem actual_component_correspondence :
    (endpointComponentGenerator twoLines a E hE).incidenceTorCorrespondence ℚ
        (X := twoLines) (Y := relativeLineSite twoLines) (Z := AffineLineField.line ℚ) G =
      (endpointComponentGenerator twoLines a E hE).incidenceFundamentalCorrespondence ℚ
        (X := twoLines) (Y := relativeLineSite twoLines) (Z := AffineLineField.line ℚ) G :=
  component_incidenceTorCorrespondence_eq_fundamental twoLines (AffineLineField.line ℚ)
    a E hE G

/-- The faithful cycle consumer includes the actual finite-image map and full
fundamental cycle, so multiplicities and component collisions remain visible. -/
theorem actual_component_pushforward :
    FiniteCorrespondence.toIntegralCycle
      ((endpointComponentGenerator twoLines a E hE).incidenceTorCorrespondence ℚ
        (X := twoLines) (Y := relativeLineSite twoLines) (Z := AffineLineField.line ℚ) G) =
      IntegralCycle.finitePushforward ((endpointComponentGenerator twoLines a E hE).incidenceMap G)
        (fundamentalCycle ((endpointComponentGenerator twoLines a E hE).incidence G)) :=
  component_toIntegralCycle_incidenceTorCorrespondence twoLines (AffineLineField.line ℚ)
    a E hE G

example : ¬ PreconnectedSpace twoLines.left :=
  MotivicTest.RelativeEndpointIncidenceTor.twoLines_not_preconnected

example : ¬ IsReduced (AdjoinRoot MotivicTest.FiniteFlatSpanEndpoints.twoDoubleSections) :=
  MotivicTest.FiniteFlatSpanEndpoints.twoDoubleSections_not_reduced

open Lean in
run_cmd do
  for name in #[``component_incidenceTorCoefficient_eq_genericMultiplicity,
      ``component_incidenceTorCorrespondence_eq_fundamental,
      ``component_toIntegralCycle_incidenceTorCorrespondence,
      ``actual_component_coefficient, ``actual_component_correspondence,
      ``actual_component_pushforward,
      ``MotivicTest.RelativeEndpointStalkTor.whole_relative_endpoint_tor] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual relative endpoint fundamental correspondences use only standard foundations."

end MotivicTest.RelativeEndpointIncidenceCycle
