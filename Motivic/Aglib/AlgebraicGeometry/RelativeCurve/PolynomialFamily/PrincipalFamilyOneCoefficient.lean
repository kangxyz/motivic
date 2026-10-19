/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyZeroCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation

/-!
# The original signed principal-family coefficient at one

The actual endpoint stalk map identifies the full face scalar cokernel with
the original source stalk. Native Euler restriction and the original principal
quotient lengths therefore identify the weighted signed coefficient with the
order of the original fraction. No component is assumed flat or reduced at
its endpoint. The global correspondence graph comparison remains separate.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyOneCoefficient`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.`
Module suffix: `PrincipalFamilyChartEndpointCoefficients`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open scoped Polynomial

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

private theorem principalEuler_germ_eq_ord {W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] (s : Γ(W, ⊤)) (x : W)
    (hx : Order.coheight x = 1) (hs : W.presheaf.germ ⊤ x (by trivial) s ≠ 0) :
    letI : Nonempty (⊤ : W.Opens) := ⟨⟨x, TopologicalSpace.Opens.mem_top x⟩⟩
    Module.principalEuler (N := W.presheaf.stalk x)
        (W.presheaf.germ ⊤ x (by trivial) s) =
      W.ord (W.germToFunctionField ⊤ s) x := by
  let : Nonempty (⊤ : W.Opens) := ⟨⟨x, TopologicalSpace.Opens.mem_top x⟩⟩
  let r := W.presheaf.germ ⊤ x (show x ∈ (⊤ : W.Opens) from trivial) s
  have hs0 : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  rw [Module.principalEuler_of_regular _ (IsSMulRegular.of_ne_zero hs),
    W.ord_germ_eq_quotient_length ⊤ s hs0 (by trivial) hx]
  have hr : LinearMap.range (LinearMap.lsmul (W.presheaf.stalk x)
      (W.presheaf.stalk x) r) =
      (Ideal.span {r} : Submodule (W.presheaf.stalk x) (W.presheaf.stalk x)) := by
    ext y
    change (∃ z, r * z = y) ↔ y ∈ Ideal.span {r}
    rw [Ideal.mem_span_singleton]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  rw [hr]

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))

/-- The actual weighted numerator-minus-denominator face coefficient at one is
the original order of the same fraction on W, with all whole-fiber lengths. -/
theorem original_one_signed_face_coefficient [IsIntegral W] [IsNoetherian W]
    [IsIntegral (parameterSpace p)]
    (a b : Γ(W, ⊤)) (x : W) (hx : Order.coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (q : FiniteFlatCurve.fiber (parameterProjection p) 1)
    (hq : FiniteFlatCurve.fiberInclusion (parameterProjection p) 1 q = endpoint p 1 x) :
    letI : IsNoetherian (parameterSpace p) := by
      have : LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
        HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
      exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection p)
    letI : Nonempty (⊤ : W.Opens) := ⟨⟨x, TopologicalSpace.Opens.mem_top x⟩⟩
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (FiniteFlatCurve.principalDivisorFaceCycle (numeratorMap p a b) (parameterProjection p) 1 -
        FiniteFlatCurve.principalDivisorFaceCycle (denominatorMap p b) (parameterProjection p) 1)
      (FiniteFlatCurve.fiberInclusion (parameterProjection p) 1 q) =
        W.ord (W.germToFunctionField ⊤ a / W.germToFunctionField ⊤ b) x := by
  let : IsNoetherian (parameterSpace p) := by
    have : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection p)
  let : Nonempty (⊤ : W.Opens) := ⟨⟨x, TopologicalSpace.Opens.mem_top x⟩⟩
  obtain ⟨hN, hD⟩ := original_divisor_maps_principalFaceConditions p a b x hx ha hb
    1 (Or.inr rfl) q hq
  have hregular (s : Γ(parameterSpace p, ⊤))
      (hs : W.presheaf.germ ⊤ x (by trivial) ((endpoint p 1).appTop s) ≠ 0)
      (v : parameterSpace p) :
      IsSMulRegular ((parameterSpace p).presheaf.stalk v)
        (FiniteFlatCurve.scalar (Scheme.sectionToAffineLine (projection p ≫ p) s) 0 v) := by
    rw [Scheme.sectionToAffineLine_zero_scalar]
    apply IsSMulRegular.of_ne_zero
    intro hz
    have hs0 : s = 0 := by
      apply germ_injective_of_isIntegral (parameterSpace p) v
        (show v ∈ (⊤ : (parameterSpace p).Opens) from trivial)
      simpa only [map_zero] using hz
    apply hs
    rw [hs0, map_zero, map_zero]
  have : Flat (parameterProjection p) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hface := FiniteFlatCurve.signed_principal_face_coefficient
    (numeratorMap p a b) (denominatorMap p b) (parameterProjection p) 1 q hN hD
    (FiniteFlatCurve.scalar_regular (parameterProjection p) 1 _)
    (hregular _ (by simpa only [numerator_one] using ha) _)
    (hregular _ (by simpa only [denominator_endpoint] using hb) _)
  rw [hq] at hface ⊢
  refine hface.trans ?_
  have : IsClosedImmersion (endpoint p 1) :=
    MorphismProperty.of_isPullback (endpoint_isPullback p 1) inferInstance
  let φ := ((endpoint p 1).stalkMap x).hom
  let := φ.toAlgebra
  have hφ : Function.Surjective φ := (endpoint p 1).stalkMap_surjective x
  have he (s : Γ(parameterSpace p, ⊤)) :
      Module.principalEuler
        (N := Module.ScalarCokernel
          ((parameterSpace p).presheaf.stalk (endpoint p 1 x))
          (FiniteFlatCurve.scalar (parameterProjection p) 1 (endpoint p 1 x)))
        (FiniteFlatCurve.scalar (Scheme.sectionToAffineLine (projection p ≫ p) s)
          0 (endpoint p 1 x)) =
      Module.principalEuler (N := W.presheaf.stalk x)
        (W.presheaf.germ ⊤ x (by trivial) ((endpoint p 1).appTop s)) := by
    have h := Module.principalEuler_scalarCokernel_of_surjective hφ
      (FiniteFlatCurve.scalar (parameterProjection p) 1 (endpoint p 1 x))
      (FiniteFlatCurve.scalar (Scheme.sectionToAffineLine (projection p ≫ p) s)
        0 (endpoint p 1 x)) (endpoint_stalk_kernel p 1 x)
    rw [Scheme.sectionToAffineLine_zero_scalar] at h
    simpa only [φ, RingHom.algebraMap_toAlgebra, endpoint_germ,
      Scheme.sectionToAffineLine_zero_scalar] using h
  rw [numeratorMap, denominatorMap, he (numerator p a b), he (denominator p b),
    numerator_one, denominator_endpoint,
    principalEuler_germ_eq_ord a x hx ha, principalEuler_germ_eq_ord b x hx hb]
  have ha0 : W.germToFunctionField ⊤ a ≠ 0 := by
    apply (map_ne_zero_iff _ (W.germToFunctionField_injective ⊤)).mpr
    exact fun h => ha (by rw [h, map_zero])
  have hb0 : W.germToFunctionField ⊤ b ≠ 0 := by
    apply (map_ne_zero_iff _ (W.germToFunctionField_injective ⊤)).mpr
    exact fun h => hb (by rw [h, map_zero])
  have h := W.ord_add_ord_ratio _ _ hb0 ha0 x
  omega

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
