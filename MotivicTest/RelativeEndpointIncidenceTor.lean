/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointIncidenceTor
public import MotivicTest.RelativeEndpointComponentTor

/-!
# Original four-factor relative endpoint Tor consumers

The actual source has two positive-dimensional connected components. At all
original component incidence points, positive Tor vanishes without assuming
flatness of the right support projection. Degree zero is the full literal
endpoint quotient length. Whole nonreduced-family tests remain imported.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteFlatCurve
open Motivic.RelativeEndpointDiagram MotivicTest.FlatPolynomialComponentRegularity

namespace MotivicTest.RelativeEndpointIncidenceTor

/-- The actual relative source used below is genuinely disconnected. -/
theorem twoLines_not_preconnected : ¬ PreconnectedSpace twoLines.left := by
  intro h
  let := h
  let L := SmoothSite.coproductInl (FiniteFlatCurveFamily.line ℚ) (FiniteFlatCurveFamily.line ℚ)
  let R := SmoothSite.coproductInr (FiniteFlatCurveFamily.line ℚ) (FiniteFlatCurveFamily.line ℚ)
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (.of (Polynomial ℚ))))
  have hc : IsClopen (Set.range L.left) :=
    ⟨L.left.isClosedEmbedding.isClosed_range, L.left.opensRange.isOpen⟩
  have hu := hc.eq_univ ⟨L.left x, x, rfl⟩
  have hl : R.left x ∈ Set.range L.left := hu.symm ▸ Set.mem_univ _
  exact (isCompl_range_inl_inr (FiniteFlatCurveFamily.line ℚ).left
    (FiniteFlatCurveFamily.line ℚ).left).disjoint.notMem_of_mem_left hl ⟨x, rfl⟩

variable (a : ℚ) (E : Set twoLines.left) (hE : E ∈ irreducibleComponents twoLines.left)
  (G : FiniteCorrespondenceGenerator (relativeLineHom twoLines.hom)
    (FiniteFlatCurveFamily.line ℚ).hom)

/-- All positive original four-factor incidence Tor groups vanish on this
genuinely disconnected relative source, with no right-support flatness premise. -/
theorem actual_fourFactor_positive
    (w : (endpointComponentGenerator twoLines a E hE).incidence G) (n : ℕ) :
    IsZero ((endpointComponentGenerator twoLines a E hE).incidenceTor G w (n + 1)) :=
  component_incidenceTor_isZero_succ twoLines (FiniteFlatCurveFamily.line ℚ) a E hE G w n

/-- The literal support point before imposing the original endpoint equation. -/
abbrev supportPoint (w : (endpointComponentGenerator twoLines a E hE).incidence G) :=
  Graph.cutPoint (ambientParameter twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom) a G.inclusion
    (componentEndpointPoint twoLines (FiniteFlatCurveFamily.line ℚ) a E hE G w)

/-- The degree-zero coefficient keeps the exact original principal quotient. -/
theorem actual_fourFactor_zero
    (w : (endpointComponentGenerator twoLines a E hE).incidence G) :
    Module.length ((endpointComponentGenerator twoLines a E hE).incidenceAmbientStalk G w)
      ((endpointComponentGenerator twoLines a E hE).incidenceTor G w 0) =
      Module.length (G.scheme.presheaf.stalk (supportPoint a E hE G w))
        ((G.scheme.presheaf.stalk (supportPoint a E hE G w)) ⧸
          Ideal.ofList [scalar
            (G.inclusion ≫ ambientParameter twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom) a
            (supportPoint a E hE G w)]) :=
  component_incidenceTor_zero_length twoLines (FiniteFlatCurveFamily.line ℚ) a E hE G w

/-- The parameter scalar supplier itself is exercised at every original support stalk. -/
theorem original_scalar_regular (c : G.scheme) :
    IsSMulRegular (G.scheme.presheaf.stalk c)
      (scalar (G.inclusion ≫
        ambientParameter twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom) a c) :=
  rightSupport_endpointScalar_regular twoLines (FiniteFlatCurveFamily.line ℚ) a G c

open Lean in
run_cmd do
  for name in #[``twoLines_not_preconnected, ``rightSupport_parameter_dominant,
      ``rightSupport_endpointScalar_regular, ``component_incidenceTor_graph_length,
      ``component_incidenceTor_zero_length, ``component_incidenceTor_isZero_succ,
      ``actual_fourFactor_positive, ``actual_fourFactor_zero, ``original_scalar_regular,
      ``MotivicTest.RelativeEndpointStalkTor.whole_relative_endpoint_tor] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original four-factor relative endpoint Tor uses only standard foundations."

end MotivicTest.RelativeEndpointIncidenceTor
