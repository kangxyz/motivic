/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PrincipalFaceCoefficient
public import Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.Surjective

/-!
# Actual principal-divisor face coefficients in the common ambient stalk

The numerator divisor is the literal zero fiber of its original map to the
affine line. Its principal stalk kernel is proved by the native fiber ideal
formula, not supplied as an input. The full original component-fiber weights
therefore compute the ambient scalar-cokernel Euler expression. Regularity is
required only on the contributing reduced component quotients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Motivic
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsNoetherian P]
  (n f : P ⟶ Spec (.of k[X])) (a : k)

omit [IsNoetherian P] in
/-- The original zero-divisor stalk Euler expression is the actual ambient
numerator scalar-cokernel expression. Its kernel and face scalar are derived
from the original two affine-line maps. -/
theorem principal_divisor_stalk_euler_eq_ambient
    (x : fiber n 0) :
    Module.principalEuler (N := (fiber n 0).presheaf.stalk x)
        (scalar (fiberInclusion n 0 ≫ f) a x) =
      Module.principalEuler
        (N := Module.ScalarCokernel (P.presheaf.stalk (fiberInclusion n 0 x))
          (scalar n 0 (fiberInclusion n 0 x)))
        (scalar f a (fiberInclusion n 0 x)) := by
  let φ := ((fiberInclusion n 0).stalkMap x).hom
  let := φ.toAlgebra
  have hφ : Function.Surjective φ := (fiberInclusion n 0).stalkMap_surjective x
  have hker : RingHom.ker φ = Ideal.span {scalar n 0 (fiberInclusion n 0 x)} := by
    rw [← (fiberInclusion n 0).ker_stalk x, fiberInclusion_stalk, Ideal.ofList_singleton]
  have he := Module.principalEuler_scalarCokernel_of_surjective hφ
    (scalar n 0 (fiberInclusion n 0 x)) (scalar f a (fiberInclusion n 0 x)) hker
  have hs : algebraMap (P.presheaf.stalk (fiberInclusion n 0 x))
      ((fiber n 0).presheaf.stalk x) (scalar f a (fiberInclusion n 0 x)) =
      scalar (fiberInclusion n 0 ≫ f) a x :=
    scalar_stalkMap f a (fiberInclusion n 0) x
  rw [hs] at he
  exact he.symm

/-- The original nonreduced numerator divisor's generic weights and complete
component fibers compute the common ambient stalk expression. No principal
kernel equation or coefficient equality is assumed. -/
theorem weighted_principal_divisor_face_coefficient
    (y : fiber (fiberInclusion n 0 ≫ f) a)
    (hcut : Module.length
      ((fiber n 0).presheaf.stalk (fiberInclusion (fiberInclusion n 0 ≫ f) a y))
      (((fiber n 0).presheaf.stalk (fiberInclusion (fiberInclusion n 0 ≫ f) a y)) ⧸
        Ideal.ofList [scalar (fiberInclusion n 0 ≫ f) a
          (fiberInclusion (fiberInclusion n 0 ≫ f) a y)]) ≠ ⊤)
    (hregular : ∀ z : genericPoints (fiber n 0),
      IsSMulRegular
        (((fiber n 0).presheaf.stalk (fiberInclusion (fiberInclusion n 0 ≫ f) a y)) ⧸
          (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι.ker.stalk
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y))
        (scalar (fiberInclusion n 0 ≫ f) a
          (fiberInclusion (fiberInclusion n 0 ≫ f) a y))) :
    let := IntegralCycle.genericPointFintype (fiber n 0)
    ∑ z : genericPoints (fiber n 0), (genericMultiplicity z : ℤ) *
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward
          (fiberMap (fiberInclusion n 0 ≫ f) a
              (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
            fiberInclusion (fiberInclusion n 0 ≫ f) a)
          (fundamentalCycle
            (fiber ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
              (fiberInclusion n 0 ≫ f)) a)))
        (fiberInclusion (fiberInclusion n 0 ≫ f) a y) =
      Module.principalEuler
        (N := Module.ScalarCokernel
          (P.presheaf.stalk (fiberInclusion n 0
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y)))
          (scalar n 0 (fiberInclusion n 0
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y))))
        (scalar f a (fiberInclusion n 0
          (fiberInclusion (fiberInclusion n 0 ≫ f) a y))) := by
  exact (weighted_component_fiber_coefficient_eq_principalEuler
    (fiberInclusion n 0 ≫ f) a y hcut hregular).trans
      (principal_divisor_stalk_euler_eq_ambient n f a _)

end AlgebraicGeometry.FiniteFlatCurve
