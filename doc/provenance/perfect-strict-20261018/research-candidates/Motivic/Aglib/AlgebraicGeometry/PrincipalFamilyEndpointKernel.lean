/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PrincipalFamilyEndpointCuts
public import Motivic.Aglib.AlgebraicGeometry.FiniteFlatCurveSpecialization

/-!
# The original parameter ideal in a polynomial endpoint stalk

The actual endpoint square is Cartesian by cancellation against the original
polynomial-product square. Pullback of the native scalar-evaluation ideal gives
the literal principal stalk kernel, without flatness or integrality assumptions.
The finite-cut consumer retains the full original numerator and denominator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open scoped Polynomial

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))

/-- The original projection to the scalar parameter line. -/
abbrev parameterProjection : parameterSpace p ⟶ Spec (.of k[X]) :=
  pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))

/-- The original endpoint, not a replacement fibre model, is Cartesian. -/
theorem endpoint_isPullback (c : k) :
    IsPullback p (endpoint p c) (FiniteFlatCurve.endpoint c) (parameterProjection p) := by
  have he : FiniteFlatCurve.endpoint c ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) = 𝟙 _ := by
    rw [FiniteFlatCurve.endpoint, ← Spec.map_comp]
    have h : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom c) = 𝟙 (CommRingCat.of k) := by
      ext r
      exact Polynomial.eval_C
    rw [h, Spec.map_id]
  have houter : IsPullback p (endpoint p c ≫ projection p)
      (FiniteFlatCurve.endpoint c ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) p := by
    rw [endpoint_projection, he]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact houter.of_bot (endpoint_snd p c).symm
    (IsPullback.of_hasPullback p
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))).flip

/-- The endpoint stalk kernel is exactly the original parameter scalar ideal. -/
theorem endpoint_stalk_kernel (c : k) (x : W) :
    RingHom.ker ((endpoint p c).stalkMap x).hom =
      Ideal.span {FiniteFlatCurve.scalar (parameterProjection p) c (endpoint p c x)} := by
  have : IsClosedImmersion (endpoint p c) :=
    MorphismProperty.of_isPullback (endpoint_isPullback p c) inferInstance
  have hk : (endpoint p c).ker =
      (FiniteFlatCurve.endpoint c).ker.comap (parameterProjection p) :=
    Motivic.ker_eq_comap_of_isPullback _ _ _ _ (endpoint_isPullback p c).flip
  rw [← (endpoint p c).ker_stalk x, hk, Scheme.IdealSheafData.stalk_comap,
    FiniteFlatCurve.endpoint_stalk, Ideal.map_ofList, List.map_cons, List.map_nil,
    Ideal.ofList_singleton]
  rfl

/-- The scalar is the germ of the literal pullback of `t-c`, with its original
ambient section retained. -/
theorem endpoint_scalar_eq_germ (c : k) (y : parameterSpace p) :
    FiniteFlatCurve.scalar (parameterProjection p) c y =
      (parameterSpace p).presheaf.germ ⊤ y (by trivial)
        ((parameterProjection p).appTop
          ((Scheme.ΓSpecIso (.of k[X])).inv (Polynomial.X - Polynomial.C c))) := by
  simp [FiniteFlatCurve.scalar, FiniteFlatCurve.endpointScalar, Scheme.Hom.appTop]

/-- Both original signed-family terms have finite complete cuts by the literal
parameter ideal. No reduced divisor or flat closed support is substituted. -/
theorem numerator_denominator_scalar_cuts_finite [IsIntegral W] [IsNoetherian W]
    (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (c : k) (hc : c = 0 ∨ c = 1)
    (s : Γ(parameterSpace p, ⊤)) (hs : s = numerator p a b ∨ s = denominator p b) :
    Module.length ((parameterSpace p).presheaf.stalk (endpoint p c x))
      (((parameterSpace p).presheaf.stalk (endpoint p c x)) ⧸
        (Ideal.ofList [FiniteFlatCurve.scalar (parameterProjection p) c (endpoint p c x)] ⊔
          Ideal.ofList [(parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
            (by trivial) s])) ≠ ⊤ := by
  have h := numerator_denominator_cuts_finite p a b x hx ha hb c hc s hs
  rw [endpoint_stalk_kernel p c x] at h
  rw [Ideal.ofList_singleton, Ideal.ofList_singleton]
  exact h

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
