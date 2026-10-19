/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointStalkTor
public import MotivicTest.GraphPolynomialTor

/-!
# Actual relative endpoint stalk Tor consumers

The relative source is the disjoint union of two affine lines. Its finite-flat
family is the literal base change of the two-double-section monic quotient.
The original root coordinate gives a proved closed embedding, and the original
triple-support Tor retains the whole endpoint quotient and its multiplicities.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme.Graph (cutPoint)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleProduct)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteFlatCurve AlgebraicGeometry.FiniteTwoUnitPolynomialFamily
open MotivicTest.FlatPolynomialComponentRegularity MotivicTest.FiniteFlatSpanEndpoints
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

namespace MotivicTest.RelativeEndpointStalkTor
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

/-- The original root coordinate on the whole finite-flat base-change family. -/
abbrev relativeRoot : relativeDoubleFamily ⟶ (AffineLineField.line ℚ).left :=
  pullback.fst (projection twoDoubleSections) (parameter twoLines) ≫ rootMap twoDoubleSections

/-- Both coordinates have the same original constant-field map. -/
theorem joint_base :
    relativeDoubleProjection ≫ relativeLineHom twoLines.hom =
      relativeRoot ≫ (AffineLineField.line ℚ).hom := by
  change relativeDoubleProjection ≫
      (pullback.fst twoLines.hom (AffineLineField.line ℚ).hom ≫ twoLines.hom) = _
  rw [pullback.condition]
  change (relativeDoubleProjection ≫ parameter twoLines) ≫
      (AffineLineField.line ℚ).hom = _
  rw [← pullback.condition, Category.assoc, rootSpanBase]
  rfl

/-- Keep the literal base and root coordinates of the unreduced family. -/
def joint : relativeDoubleFamily ⟶
    rightAmbient (relativeLineHom twoLines.hom) (AffineLineField.line ℚ).hom :=
  pullback.lift relativeDoubleProjection relativeRoot joint_base

instance : IsFinite joint :=
  FiniteFlatCorrespondence.isFinite_productMap relativeDoubleProjection joint
    (pullback.lift_fst _ _ _)

instance : Mono joint := by
  have : IsClosedImmersion (pullback.lift (projection twoDoubleSections)
      (rootMap twoDoubleSections) (rootSpanBase twoDoubleSections)) :=
    rootSpanClosed twoDoubleSections twoDoubleSections_monic
  constructor
  intro Z u v huv
  have hb : u ≫ relativeDoubleProjection = v ≫ relativeDoubleProjection := by
    simpa only [joint, Category.assoc, pullback.lift_fst] using
      congrArg (fun q => q ≫ pullback.fst _ _) huv
  have hr : u ≫ relativeRoot = v ≫ relativeRoot := by
    simpa only [joint, Category.assoc, pullback.lift_snd] using
      congrArg (fun q => q ≫ pullback.snd _ _) huv
  apply pullback.hom_ext
  · apply (cancel_mono (pullback.lift (projection twoDoubleSections)
      (rootMap twoDoubleSections) (rootSpanBase twoDoubleSections))).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [pullback.condition, ← Category.assoc, hb, Category.assoc]
    · simpa only [Category.assoc, pullback.lift_snd] using hr
  · exact hb

instance : IsClosedImmersion joint :=
  (IsClosedImmersion.iff_isFinite_and_mono joint).mpr ⟨inferInstance, inferInstance⟩

/-- The original triple ambient local ring at the actual whole endpoint. -/
abbrev tripleRing (a : ℚ) (z : fiber
    (joint ≫ ambientParameter twoLines.hom (AffineLineField.line ℚ).hom) a) : CommRingCat :=
  (correspondenceTripleProduct twoLines.hom (relativeLineHom twoLines.hom)
    (AffineLineField.line ℚ).hom).presheaf.stalk
      (endpointTriplePoint twoLines.hom (AffineLineField.line ℚ).hom a joint z)

/-- The actual two original triple-support stalk actions compute the endpoint
Koszul complex of the whole unreduced finite-flat family in every degree. -/
theorem whole_relative_endpoint_tor (a : ℚ) (z : fiber
    (joint ≫ ambientParameter twoLines.hom (AffineLineField.line ℚ).hom) a) (n : ℕ) :
    Module.length (tripleRing a z)
      (endpointStalkTor twoLines.hom (AffineLineField.line ℚ).hom a joint z n) =
      Module.length (relativeDoubleFamily.presheaf.stalk
          (cutPoint (ambientParameter twoLines.hom (AffineLineField.line ℚ).hom)
            a joint z))
        ((_root_.ChainComplex.Koszul.coefficientComplex
          (ModuleCat.of (relativeDoubleFamily.presheaf.stalk
            (cutPoint (ambientParameter twoLines.hom (AffineLineField.line ℚ).hom)
              a joint z))
            (relativeDoubleFamily.presheaf.stalk
              (cutPoint (ambientParameter twoLines.hom (AffineLineField.line ℚ).hom)
                a joint z)))
          [scalar (joint ≫ ambientParameter twoLines.hom (AffineLineField.line ℚ).hom) a
            (cutPoint (ambientParameter twoLines.hom (AffineLineField.line ℚ).hom)
              a joint z)]).homology n) :=
  endpointStalkTor_koszul_length twoLines.hom (AffineLineField.line ℚ).hom a joint z n

example : ¬ IsReduced (AdjoinRoot twoDoubleSections) := twoDoubleSections_not_reduced

example : ¬ PreconnectedSpace (familyScheme twoDoubleSections) :=
  twoDoubleSections_not_preconnected

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.Intersection.pointedStalkTor_balance_length,
      ``_root_.AlgebraicGeometry.Scheme.Graph.polynomialTor_eq_pointed, ``endpointStalkTor_length,
      ``endpointStalkTor_koszul_length, ``whole_relative_endpoint_tor] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual original relative endpoint stalk Tor uses only standard foundations."

end MotivicTest.RelativeEndpointStalkTor
