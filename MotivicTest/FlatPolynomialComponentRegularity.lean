/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.PolynomialBlock
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Coproducts
public import MotivicTest.FiniteFlatSpanEndpoints

/-!
# Relative-base component endpoint regularity consumers

A flat family over the actual product `X × A¹` has the required regular endpoint
scalar on every reduced component, with no integrality of `X` and no flatness of
the component over that product. The explicit base-change family below uses a
disjoint union of two affine lines as its relative base. The original two-double-
section quotient supplies a separate genuinely nonreduced/disconnected consumer.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (IntegralClosedSubscheme SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Graph (exists_polynomialBlock polynomialParameter
  polynomialScalar_graph)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteTwoUnitPolynomialFamily
open MotivicTest.FiniteFlatSpanEndpoints

universe u

namespace MotivicTest.FlatPolynomialComponentRegularity
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]

/-- The actual relative product, with an arbitrary smooth relative base. -/
abbrev relativeBase (X : SmoothSite (Spec (.of k))) :=
  pullback X.hom (AffineLineField.line k).hom

/-- The parameter is the actual second projection, not a chosen affine chart. -/
abbrev parameter (X : SmoothSite (Spec (.of k))) :
    relativeBase X ⟶ Spec (.of (Polynomial k)) :=
  pullback.snd X.hom (AffineLineField.line k).hom

/-- Whole-family flatness suffices, even with a disconnected smooth base. -/
theorem relative_component_regular (X : SmoothSite (Spec (.of k)))
    {D : Scheme.{u}} (f : D ⟶ relativeBase X) [Flat f]
    (z : genericPoints D) (a : k) (d : D) :
    IsSMulRegular ((D.presheaf.stalk d) ⧸
      (IntegralClosedSubscheme.pointClosure z.val).val.subschemeι.ker.stalk d)
      (FiniteFlatCurve.scalar (f ≫ parameter X) a d) :=
  flat_polynomial_component_quotient_scalar_regular (f ≫ parameter X) z a d

/-- This base consists of two positive-dimensional components. -/
abbrev twoLines : SmoothSite (Spec (.of ℚ)) :=
  SmoothSite.coproduct (AffineLineField.line ℚ) (AffineLineField.line ℚ)

/-- Extend the original monic nonreduced family to the genuine relative base. -/
abbrev relativeDoubleFamily : Scheme :=
  pullback (projection twoDoubleSections) (parameter twoLines)

/-- Its whole original finite-flat map to `twoLines × A¹`. -/
abbrev relativeDoubleProjection : relativeDoubleFamily ⟶ relativeBase twoLines :=
  pullback.snd (projection twoDoubleSections) (parameter twoLines)

instance : IsFinite relativeDoubleProjection := by
  have : IsFinite (projection twoDoubleSections) := projection_finite twoDoubleSections_monic
  unfold relativeDoubleProjection
  infer_instance

instance : Flat relativeDoubleProjection := by
  have : Flat (projection twoDoubleSections) := projection_flat twoDoubleSections_monic
  unfold relativeDoubleProjection
  infer_instance

/-- The actual finite-flat relative family has regular component endpoint scalars. -/
theorem relativeDouble_component_regular
    (z : genericPoints relativeDoubleFamily) (a : ℚ) (d : relativeDoubleFamily) :
    IsSMulRegular ((relativeDoubleFamily.presheaf.stalk d) ⧸
      (IntegralClosedSubscheme.pointClosure z.val).val.subschemeι.ker.stalk d)
      (FiniteFlatCurve.scalar (relativeDoubleProjection ≫ parameter twoLines) a d) :=
  relative_component_regular twoLines relativeDoubleProjection z a d

/-- The nonreduced disconnected original quotient is not replaced by its reduction. -/
theorem twoDouble_component_regular
    (z : genericPoints (familyScheme twoDoubleSections)) (a : ℚ)
    (d : familyScheme twoDoubleSections) :
    IsSMulRegular (((familyScheme twoDoubleSections).presheaf.stalk d) ⧸
      (IntegralClosedSubscheme.pointClosure z.val).val.subschemeι.ker.stalk d)
      (FiniteFlatCurve.scalar (projection twoDoubleSections) a d) := by
  have : Flat (projection twoDoubleSections) := projection_flat twoDoubleSections_monic
  exact flat_polynomial_component_quotient_scalar_regular (projection twoDoubleSections) z a d

example : ¬ IsReduced (AdjoinRoot twoDoubleSections) := twoDoubleSections_not_reduced

example : ¬ PreconnectedSpace (familyScheme twoDoubleSections) :=
  twoDoubleSections_not_preconnected

/-- The actual root-graph ambient local ring. -/
abbrev rootGraphStalk (x : familyScheme twoDoubleSections) : CommRingCat :=
  (pullback (rootMap twoDoubleSections ≫ (AffineLineField.line ℚ).hom)
    (AffineLineField.line ℚ).hom).presheaf.stalk
      (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (rootMap twoDoubleSections)
        (AffineLineField.line ℚ).hom x)

/-- Direct all-degree graph-block consumer on the original nonreduced quotient.
The root morphism is not assumed flat. -/
theorem twoDouble_graph_block (a : ℚ) (x : familyScheme twoDoubleSections) :
    ∃ t : List (rootGraphStalk x),
      RingTheory.Sequence.IsRegular (rootGraphStalk x) t ∧
      RingHom.ker ((_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (rootMap
        twoDoubleSections)
        (AffineLineField.line ℚ).hom).stalkMap x).hom = Ideal.ofList t ∧
      ∀ n : ℕ,
        Module.length (rootGraphStalk x)
          ((_root_.ChainComplex.Koszul.coefficientComplex (ModuleCat.of (rootGraphStalk x)
              (rootGraphStalk x))
            (t ++ [FiniteFlatCurve.scalar (polynomialParameter
              (rootMap twoDoubleSections) (AffineLineField.line ℚ).hom
              (projection twoDoubleSections)) a
              (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (rootMap twoDoubleSections)
                (AffineLineField.line ℚ).hom x)])).homology n) =
          Module.length ((familyScheme twoDoubleSections).presheaf.stalk x)
            ((_root_.ChainComplex.Koszul.coefficientComplex
              (ModuleCat.of ((familyScheme twoDoubleSections).presheaf.stalk x)
                ((familyScheme twoDoubleSections).presheaf.stalk x))
              [FiniteFlatCurve.scalar (projection twoDoubleSections) a x]).homology n) :=
  exists_polynomialBlock (rootMap twoDoubleSections) (AffineLineField.line ℚ).hom
    (projection twoDoubleSections) a x

/-- On each original component the actual scalar left by graph elimination is regular. -/
theorem twoDouble_component_graph_scalar
    (z : genericPoints (familyScheme twoDoubleSections)) (a : ℚ)
    (x : (IntegralClosedSubscheme.pointClosure z.val).val.subscheme) :
    let j := (IntegralClosedSubscheme.pointClosure z.val).val.subschemeι
    IsSMulRegular ((IntegralClosedSubscheme.pointClosure z.val).val.subscheme.presheaf.stalk x)
      ((_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (j ≫ rootMap twoDoubleSections)
          (AffineLineField.line ℚ).hom).stalkMap x
        (FiniteFlatCurve.scalar (polynomialParameter (j ≫ rootMap twoDoubleSections)
            (AffineLineField.line ℚ).hom (j ≫ projection twoDoubleSections)) a
          (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (j ≫ rootMap twoDoubleSections)
            (AffineLineField.line ℚ).hom x))) := by
  dsimp only
  rw [polynomialScalar_graph]
  have : Flat (projection twoDoubleSections) := projection_flat twoDoubleSections_monic
  exact flat_polynomial_component_scalar_regular (projection twoDoubleSections) z a x

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.Hom.isDominant_pointClosure_of_generalizing,
      ``dominant_integral_affineScalar_isSMulRegular,
      ``flat_polynomial_component_scalar_regular,
      ``flat_polynomial_component_quotient_scalar_regular,
      ``relative_component_regular, ``relativeDouble_component_regular,
      ``twoDouble_component_regular, ``_root_.AlgebraicGeometry.Scheme.Graph.polynomialScalar_graph,
      ``_root_.AlgebraicGeometry.Scheme.Graph.polynomialBlock_length,
          ``_root_.AlgebraicGeometry.Scheme.Graph.exists_polynomialBlock,
      ``twoDouble_graph_block, ``twoDouble_component_graph_scalar] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Relative component endpoint regularity uses only standard foundations."

end MotivicTest.FlatPolynomialComponentRegularity
