/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PolynomialBoundaryPencil
public import Motivic.AlgebraicGeometry.Cycles.FundamentalInvariance
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Original polynomial numerator and denominator cuts at the endpoints

The numerator is literally `t*a + (1-t)*b` on the original polynomial product.
The endpoint stalk maps recover the original section germs. At a coheight-one
point of the integral Noetherian source, their nonzero images give finite full
quotient lengths. The ambient ideal uses the actual endpoint stalk kernel;
identifying this kernel with the parameter scalar ideal remains separate.
Existence of a local numerator/denominator for a specified rational function is
not asserted. No quotient is reduced, and no flatness of a support is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u v

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

/-- Surjective restriction retains the complete local quotient length. -/
private theorem quotient_length_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (n : R) :
    Module.length R (R ⧸ (RingHom.ker φ ⊔ Ideal.span {n})) =
      Module.length S (S ⧸ Ideal.span {φ n}) := by
  let ψ := (Ideal.Quotient.mk (Ideal.span {φ n})).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
  have hk : RingHom.ker ψ = RingHom.ker φ ⊔ Ideal.span {n} := by
    dsimp only [ψ]
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, sup_comm]
  let e : (R ⧸ (RingHom.ker φ ⊔ Ideal.span {n})) ≃+* (S ⧸ Ideal.span {φ n}) :=
    (Ideal.quotEquivOfEq hk.symm).trans (ψ.quotientKerEquivOfSurjective hψ)
  exact (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective
    (I := RingHom.ker φ ⊔ Ideal.span {n}))).trans
      ((Motivic.ringLength_eq_of_ringEquiv e).trans
        (Module.length_eq_of_surjective
          (Ideal.Quotient.mk_surjective (I := Ideal.span {φ n}))).symm)

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))

/-- The original polynomial numerator, without choosing a divisor replacement. -/
def numerator (a b : Γ(W, ⊤)) : Γ(parameterSpace p, ⊤) :=
  parameter p * (projection p).appTop a +
    (1 - parameter p) * (projection p).appTop b

/-- The unchanged polar denominator. -/
def denominator (b : Γ(W, ⊤)) : Γ(parameterSpace p, ⊤) :=
  (projection p).appTop b

private theorem endpoint_projection_section (c : k) (s : Γ(W, ⊤)) :
    (endpoint p c).appTop ((projection p).appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, endpoint_projection]
  simp

@[simp] theorem numerator_zero (a b : Γ(W, ⊤)) :
    (endpoint p 0).appTop (numerator p a b) = b := by
  simp [numerator, endpoint_parameter, endpoint_projection_section]

@[simp] theorem numerator_one (a b : Γ(W, ⊤)) :
    (endpoint p 1).appTop (numerator p a b) = a := by
  simp [numerator, endpoint_parameter, endpoint_projection_section]

@[simp] theorem denominator_endpoint (b : Γ(W, ⊤)) (c : k) :
    (endpoint p c).appTop (denominator p b) = b :=
  endpoint_projection_section p c b

private theorem endpoint_closed (c : k) : IsClosedImmersion (endpoint p c) := by
  have : IsSeparated (projection p) := MorphismProperty.pullback_fst _ _ inferInstance
  have : IsClosedImmersion (endpoint p c ≫ projection p) := by
    rw [endpoint_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (endpoint p c) (projection p)

/-- Restriction is through the actual original endpoint stalk map. -/
theorem endpoint_germ (c : k) (x : W) (s : Γ(parameterSpace p, ⊤)) :
    (endpoint p c).stalkMap x
        ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s) =
      W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) := by
  simp [Scheme.Hom.appTop]

/-- A nonzero original face germ gives finite length of the full ambient cut.
The kernel is the actual endpoint map's kernel, not a supplied principal ideal. -/
theorem endpoint_cut_finite [IsIntegral W] [IsNoetherian W]
    (c : k) (x : W) (hx : coheight x = 1) (s : Γ(parameterSpace p, ⊤))
    (hs : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) ≠ 0) :
    Module.length ((parameterSpace p).presheaf.stalk (endpoint p c x))
      (((parameterSpace p).presheaf.stalk (endpoint p c x)) ⧸
        (RingHom.ker ((endpoint p c).stalkMap x).hom ⊔
          Ideal.span {(parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
            (by trivial) s})) ≠ ⊤ := by
  have := endpoint_closed p c
  let φ := ((endpoint p c).stalkMap x).hom
  rw [quotient_length_of_surjective φ ((endpoint p c).stalkMap_surjective x)]
  have : Ring.KrullDimLE 1 (W.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hnonzero : φ ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
      (by trivial) s) ≠ 0 := by
    change (endpoint p c).stalkMap x
      ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s) ≠ 0
    rwa [endpoint_germ]
  exact Module.length_ne_top_iff.mpr
    (isFiniteLength_quotient_span_singleton (W.presheaf.stalk x)
      (mem_nonZeroDivisors_iff_ne_zero.mpr hnonzero))

/-- Both literal signed-family terms have nonzero original images and finite
whole cuts at zero and one. No termwise reduction or cancellation is performed. -/
theorem numerator_denominator_cuts_finite [IsIntegral W] [IsNoetherian W]
    (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (c : k) (hc : c = 0 ∨ c = 1)
    (s : Γ(parameterSpace p, ⊤)) (hs : s = numerator p a b ∨ s = denominator p b) :
    Module.length ((parameterSpace p).presheaf.stalk (endpoint p c x))
      (((parameterSpace p).presheaf.stalk (endpoint p c x)) ⧸
        (RingHom.ker ((endpoint p c).stalkMap x).hom ⊔
          Ideal.span {(parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
            (by trivial) s})) ≠ ⊤ := by
  apply endpoint_cut_finite p c x hx s
  rcases hs with rfl | rfl
  · rcases hc with rfl | rfl
    · simpa only [numerator_zero] using hb
    · simpa only [numerator_one] using ha
  · simpa only [denominator_endpoint] using hb

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
