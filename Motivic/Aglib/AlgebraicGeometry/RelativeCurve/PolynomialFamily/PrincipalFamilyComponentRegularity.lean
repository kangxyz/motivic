/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyEndpointRegularity
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.SignedPrincipalFaceCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Multiplicity.ComponentStalkRegularity

/-!
# Actual principal-divisor component regularity at the original endpoints

The full principal quotient is identified with the original closed divisor
stalk by its canonical closed-immersion linear equivalence. Scalar restriction
then gives regularity on every actual generic component, including the zero
quotient outside a component. Numerator and denominator nonvanishing and finite
cuts are derived from their literal endpoint evaluations. The affine-line map's
coordinate section is identified explicitly with the chosen original term;
no component identification, regularity family, or support flatness is assumed.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyComponentRegularity`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyDivisorMaps`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open scoped Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

/-- Transfer through the literal zero-divisor stalk, retaining its nilpotents
before passing to the original generic-component quotient. -/
theorem principal_component_regular_of_ambient_quotient
    {k : Type u} [Field k] {P : Scheme.{u}}
    (n f : P ⟶ Spec (.of k[X])) (c : k) (y : fiber n 0)
    (h : IsSMulRegular
      ((P.presheaf.stalk (fiberInclusion n 0 y)) ⧸
        Ideal.span {scalar n 0 (fiberInclusion n 0 y)})
      (scalar f c (fiberInclusion n 0 y)))
    (z : genericPoints (fiber n 0)) :
    IsSMulRegular (((fiber n 0).presheaf.stalk y) ⧸
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          z.1).val.subschemeι.ker.stalk y)
      (scalar (fiberInclusion n 0 ≫ f) c y) := by
  apply _root_.AlgebraicGeometry.Scheme.component_quotient_regular_of_stalk_regular
  let e := _root_.AlgebraicGeometry.Scheme.Hom.closedStalkQuotientLinearEquiv
    (fiberInclusion n 0) y
  have hq : IsSMulRegular
      ((P.presheaf.stalk (fiberInclusion n 0 y)) ⧸
        (fiberInclusion n 0).ker.stalk (fiberInclusion n 0 y))
      (scalar f c (fiberInclusion n 0 y)) := by
    rwa [fiberInclusion_stalk, Ideal.ofList_singleton]
  have ht := (e.isSMulRegular_congr _).mp hq
  dsimp only [scalar] at ht ⊢
  rw [Scheme.Hom.stalkMap_comp]
  convert! ht using 1

end AlgebraicGeometry.FiniteFlatCurve

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} [IsIntegral W]
  (p : W ⟶ Spec (.of k))

/-- Every original component of either literal principal term has a regular
face scalar. The displayed point lies on the actual nonreduced divisor. -/
theorem numerator_denominator_actual_component_regular
    (a b : Γ(W, ⊤)) (x : W)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (c : k) (hc : c = 0 ∨ c = 1)
    (n : parameterSpace p ⟶ Spec (.of k[X]))
    (hn : n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X) = numerator p a b ∨
      n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X) = denominator p b)
    (y : FiniteFlatCurve.fiber n 0)
    (hy : FiniteFlatCurve.fiberInclusion n 0 y = endpoint p c x)
    (z : genericPoints (FiniteFlatCurve.fiber n 0)) :
    IsSMulRegular (((FiniteFlatCurve.fiber n 0).presheaf.stalk y) ⧸
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          z.1).val.subschemeι.ker.stalk y)
      (FiniteFlatCurve.scalar (FiniteFlatCurve.fiberInclusion n 0 ≫ parameterProjection p)
        c y) := by
  apply FiniteFlatCurve.principal_component_regular_of_ambient_quotient
  have h := (numerator_denominator_endpoint_regularity p a b x ha hb c hc
    (n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X)) hn).1
  have hs (q : parameterSpace p) : FiniteFlatCurve.scalar n 0 q =
      (parameterSpace p).presheaf.germ ⊤ q (by trivial)
        (n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X)) := by
    simp [FiniteFlatCurve.scalar, FiniteFlatCurve.endpointScalar, Scheme.Hom.appTop]
  rw [hs, hy]
  exact h

private instance parameterSpace_noetherian [IsNoetherian W] :
    IsNoetherian (parameterSpace p) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection p)

/-- The actual finite-cut and component-regularity record for either original
term, at a coheight-one endpoint point. No cycle comparison is an input. -/
theorem numerator_denominator_principalFaceConditions [IsNoetherian W]
    (a b : Γ(W, ⊤)) (x : W) (hx : Order.coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (c : k) (hc : c = 0 ∨ c = 1)
    (n : parameterSpace p ⟶ Spec (.of k[X]))
    (hn : n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X) = numerator p a b ∨
      n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X) = denominator p b)
    (q : FiniteFlatCurve.fiber (parameterProjection p) c)
    (hq : FiniteFlatCurve.fiberInclusion (parameterProjection p) c q = endpoint p c x) :
    FiniteFlatCurve.PrincipalFaceConditions n (parameterProjection p) c q := by
  constructor
  · have h := numerator_denominator_scalar_cuts_finite p a b x hx ha hb c hc
      (n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X)) hn
    have hs (v : parameterSpace p) : FiniteFlatCurve.scalar n 0 v =
        (parameterSpace p).presheaf.germ ⊤ v (by trivial)
          (n.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X)) := by
      simp [FiniteFlatCurve.scalar, FiniteFlatCurve.endpointScalar, Scheme.Hom.appTop]
    rw [hs, hq]
    exact h
  · intro y hy z
    exact numerator_denominator_actual_component_regular p a b x ha hb c hc n hn
      (FiniteFlatCurve.fiberInclusion
        (FiniteFlatCurve.fiberInclusion n 0 ≫ parameterProjection p) c y)
      (hy.trans hq) z

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
