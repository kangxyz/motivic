/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.PolynomialTor
public import MotivicTest.FlatPolynomialComponentRegularity

/-!
# Literal graph-plus-endpoint Tor on a genuine relative family

The relative base is the disjoint union of two affine lines. The whole family
is the original base change of the two-double-section quotient, with its actual
finite-flat map. Component positive-Tor vanishing is derived from the whole
parameter's flatness, without assuming component flatness over the relative base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (IntegralClosedSubscheme)
open _root_.AlgebraicGeometry.Scheme.Graph (cutPoint polynomialAmbientStalk polynomialTor
  polynomialTor_component_isZero_succ polynomialTor_length polynomialTor_zero_length)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteFlatCurve
open MotivicTest.FlatPolynomialComponentRegularity

namespace MotivicTest.GraphPolynomialTor
open _root_.AlgebraicGeometry.Scheme.SmoothSite

/-- The original finite-flat family's projection to its two-component relative base. -/
abbrev relativeSource : relativeDoubleFamily ⟶ twoLines.left :=
  relativeDoubleProjection ≫ pullback.fst twoLines.hom (AffineLineField.line ℚ).hom

/-- The original family's parameter, retaining its whole structure. -/
abbrev relativeParameter : relativeDoubleFamily ⟶ Spec (.of (Polynomial ℚ)) :=
  relativeDoubleProjection ≫ parameter twoLines

instance : Flat relativeSource := inferInstance

instance : Flat relativeParameter := inferInstance

/-- The genuine actual Tor of each component has no positive-degree terms. -/
theorem relative_component_tor_succ
    (v : genericPoints relativeDoubleFamily) (a : ℚ)
    (z : fiber ((IntegralClosedSubscheme.pointClosure v.val).val.subschemeι ≫ relativeParameter) a)
    (n : ℕ) :
    IsZero (polynomialTor relativeSource twoLines.hom relativeParameter a
      (IntegralClosedSubscheme.pointClosure v.val).val.subschemeι z (n + 1)) :=
  polynomialTor_component_isZero_succ relativeSource twoLines.hom relativeParameter a v z n

/-- The degree-zero coefficient is the actual local endpoint quotient length. -/
theorem relative_component_tor_zero
    (v : genericPoints relativeDoubleFamily) (a : ℚ)
    (z : fiber
      ((IntegralClosedSubscheme.pointClosure v.val).val.subschemeι ≫ relativeParameter) a) :
    let j := (IntegralClosedSubscheme.pointClosure v.val).val.subschemeι
    Module.length (polynomialAmbientStalk
        relativeSource twoLines.hom relativeParameter a j z)
      (polynomialTor relativeSource twoLines.hom relativeParameter a j z 0) =
      Module.length ((IntegralClosedSubscheme.pointClosure v.val).val.subscheme.presheaf.stalk
        (cutPoint relativeParameter a j z))
        (((IntegralClosedSubscheme.pointClosure v.val).val.subscheme.presheaf.stalk
          (cutPoint relativeParameter a j z)) ⧸
          Ideal.ofList [scalar (j ≫ relativeParameter) a
            (cutPoint relativeParameter a j z)]) :=
  polynomialTor_zero_length relativeSource twoLines.hom relativeParameter a _ z

/-- The same local Tor calculation also applies to the whole original support.
This is not merely a test on an integral component. -/
theorem relative_whole_tor_length (a : ℚ) (z : fiber (𝟙 relativeDoubleFamily ≫ relativeParameter) a)
    (n : ℕ) :
    Module.length (polynomialAmbientStalk relativeSource twoLines.hom relativeParameter a
        (𝟙 relativeDoubleFamily) z)
      (polynomialTor relativeSource twoLines.hom relativeParameter a
        (𝟙 relativeDoubleFamily) z n) =
      Module.length (relativeDoubleFamily.presheaf.stalk
          (cutPoint relativeParameter a (𝟙 relativeDoubleFamily) z))
        ((_root_.ChainComplex.Koszul.coefficientComplex
          (ModuleCat.of (relativeDoubleFamily.presheaf.stalk
            (cutPoint relativeParameter a (𝟙 relativeDoubleFamily) z))
            (relativeDoubleFamily.presheaf.stalk
              (cutPoint relativeParameter a (𝟙 relativeDoubleFamily) z)))
          [scalar (𝟙 relativeDoubleFamily ≫ relativeParameter) a
            (cutPoint relativeParameter a (𝟙 relativeDoubleFamily) z)]).homology n) :=
  polynomialTor_length relativeSource twoLines.hom relativeParameter a
    (𝟙 relativeDoubleFamily) z n

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.Graph.exists_common_graphKernel,
      ``_root_.AlgebraicGeometry.Scheme.Graph.polynomialTor_length,
      ``_root_.AlgebraicGeometry.Scheme.Graph.polynomialTor_zero_length,
          ``_root_.AlgebraicGeometry.Scheme.Graph.polynomialTor_isZero_succ_of_scalar_regular,
      ``_root_.AlgebraicGeometry.Scheme.Graph.polynomialTor_component_isZero_succ,
          ``relative_component_tor_succ,
      ``relative_component_tor_zero, ``relative_whole_tor_length] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual relative graph-plus-endpoint Tor uses only standard foundations."

end MotivicTest.GraphPolynomialTor
