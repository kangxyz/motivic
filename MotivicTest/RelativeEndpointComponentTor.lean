/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointComponentTor
public import MotivicTest.RelativeEndpointStalkTor

/-!
# Disconnected-source component endpoint consumers

At every actual incidence point of either component graph of the two-line
source, both original pulled ideal supports have the graph-block Tor length.
All points and compatibility proofs come from the original incidence maps.
No integrality of the two-line source or flatness of the right support is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.RelativeEndpointDiagram MotivicTest.FlatPolynomialComponentRegularity

namespace MotivicTest.RelativeEndpointComponentTor

variable (a : ℚ) (E : Set twoLines.left) (hE : E ∈ irreducibleComponents twoLines.left)
  (G : FiniteCorrespondenceGenerator (relativeLineHom twoLines.hom)
    (FiniteFlatCurveFamily.line ℚ).hom)

abbrev leftGraph := endpointComponentGenerator twoLines a E hE

/-- The canonical map from the original incidence to its left pulled ideal support. -/
def leftPointMap :=
  pullback.lift ((leftGraph a E hE).incidenceInclusion G)
    ((leftGraph a E hE).incidenceFst G) ((leftGraph a E hE).incidenceInclusion_fst G) ≫
      ((leftGraph a E hE).val.comapIso _).inv

/-- The canonical map to the original right pulled ideal support. -/
def rightPointMap :=
  pullback.lift ((leftGraph a E hE).incidenceInclusion G)
    ((leftGraph a E hE).incidenceSnd G) ((leftGraph a E hE).incidenceInclusion_snd G) ≫
      (G.val.comapIso _).inv

/-- The literal endpoint-fiber point supplied by this component incidence. -/
abbrev endpointPoint (w : (leftGraph a E hE).incidence G) :=
  incidenceToEndpointFiber twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom a
    (leftGraph a E hE) G (endpointComponentGenerator_target twoLines a E hE) w

/-- The original left support image agrees with the actual whole endpoint point. -/
theorem leftPoint_image (w : (leftGraph a E hE).incidence G) :
    originalLeftInclusion twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom (leftGraph a E hE)
        (leftPointMap a E hE G w) =
      endpointTriplePoint twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom a G.inclusion
        (endpointPoint a E hE G w) := by
  rw [endpointComponent_incidence_point]
  exact congrArg (fun q => q w) (show leftPointMap a E hE G ≫
    originalLeftInclusion twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom (leftGraph a E hE) =
      (leftGraph a E hE).incidenceInclusion G by
        simp [leftPointMap, originalLeftInclusion])

/-- The original right support image has the identical actual ambient point. -/
theorem rightPoint_image (w : (leftGraph a E hE).incidence G) :
    originalRightInclusion twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom G
        (rightPointMap a E hE G w) =
      endpointTriplePoint twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom a G.inclusion
        (endpointPoint a E hE G w) := by
  rw [endpointComponent_incidence_point]
  exact congrArg (fun q => q w) (show rightPointMap a E hE G ≫
    originalRightInclusion twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom G =
      (leftGraph a E hE).incidenceInclusion G by
        simp [rightPointMap, originalRightInclusion])

/-- Every actual component incidence on the disconnected base has the proved
original pulled-ideal Tor length, with both original scalar actions. -/
theorem disconnected_component_pulled_tor (w : (leftGraph a E hE).incidence G) (n : ℕ) :
    Module.length
      ((correspondenceTripleProduct twoLines.hom (relativeLineHom twoLines.hom)
        (FiniteFlatCurveFamily.line ℚ).hom).presheaf.stalk
        (endpointTriplePoint twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom a G.inclusion
          (endpointPoint a E hE G w)))
      (originalComponentPulledTor twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom a
        (leftGraph a E hE) G (endpointPoint a E hE G w)
        (leftPointMap a E hE G w) (rightPointMap a E hE G w)
        (leftPoint_image a E hE G w) (rightPoint_image a E hE G w) n) =
      Module.length
        (Graph.polynomialAmbientStalk
          (endpointAmbientSource twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom) twoLines.hom
          (ambientParameter twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom) a G.inclusion
          (endpointPoint a E hE G w))
        (Graph.polynomialTor
          (endpointAmbientSource twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom) twoLines.hom
          (ambientParameter twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom) a G.inclusion
          (endpointPoint a E hE G w) n) :=
  originalComponentPulledTor_length twoLines.hom (FiniteFlatCurveFamily.line ℚ).hom a
    (leftGraph a E hE) G (endpointComponentGenerator_target twoLines a E hE)
    (endpointPoint a E hE G w) (leftPointMap a E hE G w) (rightPointMap a E hE G w)
    (leftPoint_image a E hE G w) (rightPoint_image a E hE G w) n

open Lean in
run_cmd do
  for name in #[``componentLeftToWhole_inclusion, ``originalRightToWhole_inclusion,
      ``endpointComponent_left_open, ``endpointComponent_incidence_point,
      ``originalComponentPulledTor_length, ``disconnected_component_pulled_tor] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual disconnected component endpoint transport uses only standard foundations."

end MotivicTest.RelativeEndpointComponentTor
