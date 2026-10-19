/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyDivisorMaps

/-!
# The actual signed principal-family coefficient at zero

The canonical numerator and denominator maps supply their complete nonreduced
face cycles. Their original coordinate germs satisfy the literal zero-face
congruence. Full principal-face conditions and scalar regularity are derived
from the original endpoint data before applying native Euler cancellation.
This is a local weighted geometric coefficient theorem, not yet the comparison
with the global finite correspondence's graph endpoint.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyZeroCoefficient`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.`
Module suffix: `PrincipalFamilyChartEndpointCoefficients`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.PrincipalSectionOrderCycle`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyOneCoefficient`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

/-- The zero scalar of the canonical section map is the original section germ. -/
theorem sectionToAffineLine_zero_scalar {R : Type u} [Field R] {P : Scheme.{u}}
    (p : P ⟶ Spec (.of R)) (s : Γ(P, ⊤)) (x : P) :
    FiniteFlatCurve.scalar (sectionToAffineLine p s) 0 x =
      P.presheaf.germ ⊤ x (by trivial) s := by
  have h : FiniteFlatCurve.scalar (sectionToAffineLine p s) 0 x =
      P.presheaf.germ ⊤ x (by trivial)
        ((sectionToAffineLine p s).appTop ((ΓSpecIso (.of R[X])).inv Polynomial.X)) := by
    simp [FiniteFlatCurve.scalar, FiniteFlatCurve.endpointScalar, Scheme.Hom.appTop]
  rw [h, sectionToAffineLine_coordinate]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}}
  (p : W ⟶ Spec (.of k))

/-- The two original pushed weighted divisor-face cycles cancel at zero,
including mixed or empty support and all nonreduced local multiplicities. -/
theorem original_zero_signed_face_coefficient [IsIntegral W] [IsNoetherian W]
    [IsIntegral (parameterSpace p)]
    (a b : Γ(W, ⊤)) (x : W) (hx : Order.coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (q : FiniteFlatCurve.fiber (parameterProjection p) 0)
    (hq : FiniteFlatCurve.fiberInclusion (parameterProjection p) 0 q = endpoint p 0 x) :
    letI : IsNoetherian (parameterSpace p) := by
      have : LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
        HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
      exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection p)
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (FiniteFlatCurve.principalDivisorFaceCycle (numeratorMap p a b) (parameterProjection p) 0 -
        FiniteFlatCurve.principalDivisorFaceCycle (denominatorMap p b) (parameterProjection p) 0)
      (FiniteFlatCurve.fiberInclusion (parameterProjection p) 0 q) = 0 := by
  let : IsNoetherian (parameterSpace p) := by
    have : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection p)
  obtain ⟨hN, hD⟩ := original_divisor_maps_principalFaceConditions p a b x hx ha hb
    0 (Or.inl rfl) q hq
  let v := FiniteFlatCurve.fiberInclusion (parameterProjection p) 0 q
  let γ := (parameterSpace p).presheaf.germ ⊤ v
    (show v ∈ (⊤ : (parameterSpace p).Opens) from trivial)
  have hNscalar : FiniteFlatCurve.scalar (numeratorMap p a b) 0 v = γ (numerator p a b) :=
    Scheme.sectionToAffineLine_zero_scalar _ _ _
  have hDscalar : FiniteFlatCurve.scalar (denominatorMap p b) 0 v = γ (denominator p b) :=
    Scheme.sectionToAffineLine_zero_scalar _ _ _
  have ht : FiniteFlatCurve.scalar (parameterProjection p) 0 v = γ (parameter p) := by
    simpa [parameter, γ] using endpoint_scalar_eq_germ p 0 v
  have hnonzero (s : Γ(parameterSpace p, ⊤))
      (hs : (endpoint p 0).appTop s = b) : γ s ≠ 0 := by
    intro hz
    have hs0 : s = 0 := by
      apply germ_injective_of_isIntegral (parameterSpace p) v
        (show v ∈ (⊤ : (parameterSpace p).Opens) from trivial)
      simpa only [map_zero] using hz
    apply hb
    rw [← hs, hs0, map_zero, map_zero]
  have hnr : IsSMulRegular ((parameterSpace p).presheaf.stalk v)
      (FiniteFlatCurve.scalar (numeratorMap p a b) 0 v) := by
    rw [hNscalar]
    exact IsSMulRegular.of_ne_zero (hnonzero _ (numerator_zero p a b))
  have hdr : IsSMulRegular ((parameterSpace p).presheaf.stalk v)
      (FiniteFlatCurve.scalar (denominatorMap p b) 0 v) := by
    rw [hDscalar]
    exact IsSMulRegular.of_ne_zero (hnonzero _ (denominator_endpoint p b 0))
  have : Flat (parameterProjection p) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  apply FiniteFlatCurve.signed_principal_face_coefficient_eq_zero
    (numeratorMap p a b) (denominatorMap p b) (parameterProjection p) 0 q hN hD
    (FiniteFlatCurve.scalar_regular (parameterProjection p) 0 _) hnr hdr
    (γ ((projection p).appTop a - (projection p).appTop b))
  change FiniteFlatCurve.scalar (numeratorMap p a b) 0 v =
    FiniteFlatCurve.scalar (denominatorMap p b) 0 v +
      FiniteFlatCurve.scalar (parameterProjection p) 0 v * _
  rw [hNscalar, hDscalar, ht]
  simp only [numerator, denominator, map_add, map_mul, map_sub, map_one]
  ring

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
