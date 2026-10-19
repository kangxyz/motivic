/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberProjection

/-!
# Support of the original signed projected component sum

Each nonzero original component is finite and dominant over the unchanged
parameter cylinder. Its actual whole face has already been placed in the
retained smooth curve. Additivity shows that signed collisions cannot introduce
support outside codimension one; no coheight family is supplied as an input.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberProjectionSupport`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyWholeEndpoints`.
-/

open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
  (componentFaceCurveMap_coefficient_coheight)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve AlgebraicGeometry.PrincipalFamilyUnitOpen

open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.IntegralCycle

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  [IsAffine X.left] [IsIntegral X.left]
  {V : Scheme.{u}} (q : V ⟶ X.left) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  [IsNoetherian (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine (q ≫
      X.hom))]
  (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine (q ≫ X.hom)))
  (hfinite : ∀ Z ∈ c.support, IsFinite (Z.val.subschemeι ≫ lineMap X.hom q))
  (hdominant : ∀ Z ∈ c.support, IsDominant (Z.val.subschemeι ≫ lineMap X.hom q))

include hfinite hdominant in
/-- The actual weighted projection vanishes at every point not of coheight one.
The proof uses whole original face multiplicities before allowing signed collisions. -/
theorem wholeComponentFiber_projection_eq_zero_of_coheight_ne
    (a : k) (y : V) (hy : Order.coheight y ≠ 1) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
      (pullback.fst (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
          k).hom)
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber
        (pullback.snd (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
            k).hom) a c)) y = 0 := by
  classical
  let F : _root_.AlgebraicGeometry.Scheme.IntegralCycle
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine (q ≫ X.hom)) →+
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle V :=
    (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
      (pullback.fst (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
          k).hom)).comp
      (toPoints.comp (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber
        (pullback.snd (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
            k).hom) a))
  change F c y = 0
  have he : F c y = c.sum (fun Z n => F (Finsupp.single Z n) y) := by
    conv_lhs => rw [← c.sum_single]
    simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  rw [he]
  apply Finset.sum_eq_zero
  intro Z hZ
  let : IsFinite (Z.val.subschemeι ≫ lineMap X.hom q) := hfinite Z hZ
  let : IsDominant (Z.val.subschemeι ≫ lineMap X.hom q) := hdominant Z hZ
  have hz : _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.componentFaceCurveMap (q
          ≫ X.hom) Z.val.subschemeι a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber
            (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter (q ≫
            X.hom) Z.val.subschemeι) a))) y = 0 := by
    by_contra hn
    exact hy (componentFaceCurveMap_coefficient_coheight X q Z.val.subschemeι a y hn)
  change _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
    (pullback.fst (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
        k).hom)
    (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber
      (pullback.snd (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
          k).hom) a
      (Finsupp.single Z (c Z)))) y = 0
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_projection_single]
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
      _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle] at hz
  simp only [Finsupp.smul_apply, hz, smul_zero]

include hfinite hdominant in
/-- Every nonzero coefficient of the original signed projected sum is placed in
coheight one by geometry, even when several original components collide. -/
theorem wholeComponentFiber_projection_coheight
    (a : k) (y : V)
    (hy : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
      (pullback.fst (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
          k).hom)
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber
        (pullback.snd (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
            k).hom) a c)) y ≠ 0) :
    Order.coheight y = 1 := by
  by_contra hn
  exact hy (wholeComponentFiber_projection_eq_zero_of_coheight_ne X q c hfinite hdominant a y hn)

end AlgebraicGeometry.Scheme.IntegralCycle
