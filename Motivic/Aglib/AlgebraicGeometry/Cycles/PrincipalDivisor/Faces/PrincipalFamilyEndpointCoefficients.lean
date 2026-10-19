/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartEndpointCoefficients

/-!
# Original principal-family coefficients without chart choices

At each codimension-one point of the original curve, the affine neighborhood,
nonzero fraction, and whole face points are constructed internally. The ambient
product remains explicitly integral. Nonvanishing of the original function is
not inferred from an empty boundary or from the family's nonempty unit locus.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyEndpointCoefficients`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyWholeEndpoints`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open scoped Polynomial

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

open PrincipalFamilyEndpointCuts

attribute [local instance] Scheme.functionField_openImmersion_dominant
  Scheme.functionField_nonempty_preimage Scheme.nonempty_image_open

local instance {P : Scheme.{u}} [IsIntegral P] : Nonempty (⊤ : P.Opens) :=
  ⟨⟨genericPoint P, TopologicalSpace.Opens.mem_top (genericPoint P)⟩⟩

private theorem exists_chart_face_point
    {k : Type u} [Field k] {C : Scheme.{u}} (p : C ⟶ Spec (.of k))
    (U : C.Opens) (x : U.toScheme) (c : k) :
    ∃ z : fiber (parameterProjection (U.ι ≫ p)) c,
      fiberInclusion (parameterProjection (U.ι ≫ p)) c z = endpoint (U.ι ≫ p) c x ∧
      lineMap p U.ι (fiberInclusion (parameterProjection (U.ι ≫ p)) c z) =
        endpoint p c (U.ι x) := by
  have he : FiniteFlatCurve.endpoint c ((U.ι ≫ p) x) =
      parameterProjection (U.ι ≫ p) (endpoint (U.ι ≫ p) c x) := by
    have h := congrArg (fun g => g x) (endpoint_snd (U.ι ≫ p) c)
    exact h.symm
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (FiniteFlatCurve.endpoint c)
      (parameterProjection (U.ι ≫ p))) ((U.ι ≫ p) x) (endpoint (U.ι ≫ p) c x) he
  refine ⟨z, hz, ?_⟩
  rw [hz]
  have hn : endpoint (U.ι ≫ p) c ≫ lineMap p U.ι = U.ι ≫ endpoint p c := by
    change endpoint (U.ι ≫ p) c ≫ parameterMap p U.ι = U.ι ≫ endpoint p c
    exact endpoint_parameterMap p U.ι c
  exact congrArg (fun g => g x) hn

/-- Both original endpoint coefficients, with every affine fraction and face
point constructed from the original nonzero function and original point. -/
theorem originalOrderCycle_endpoint_coefficients
    {k : Type u} [Field k] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) (v : W ⟶ C) [IsOpenImmersion v]
    [IsIntegral C] [IsNoetherian C] [IsIntegral W]
    [IsIntegral (parameterSpace p)] [IsNoetherian (parameterSpace p)]
    [IsIntegral (parameterSpace (v ≫ p))]
    (f : Γ(W, ⊤)) (hf : f ≠ 0)
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
    (x : C) (hx : Order.coheight x = 1) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (parameterProjection p) 0
        (originalOrderCycle p v f)) (endpoint p 0 x) = 0 ∧
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (parameterProjection p) 1
        (originalOrderCycle p v f)) (endpoint p 1 x) =
      C.ord (C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)) x := by
  have hr : C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f) ≠ 0 := by
    apply (map_ne_zero_iff _ (C.germToFunctionField_injective _)).mpr
    intro h
    apply hf
    simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero]
      using congrArg (v.appIso ⊤).hom h
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : C.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let xU : U.toScheme := ⟨x, hxU⟩
  let : IsNoetherian U.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (U : Set C)) }
  let : Nonempty (parameterSpace (U.ι ≫ p)) := ⟨endpoint (U.ι ≫ p) 0 xU⟩
  let : IsIntegral (parameterSpace (U.ι ≫ p)) :=
    isIntegral_of_isOpenImmersion (lineMap p U.ι)
  let : IsNoetherian (parameterSpace (U.ι ≫ p)) := by
    have : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection (U.ι ≫ p))
  obtain ⟨a, b, hn, hab⟩ := C.exists_nonzero_affine_fraction U hU _ hr
  have ha : a ≠ 0 := fun hz => (hn x hxU).1 (by rw [hz, map_zero])
  have hb : b ≠ 0 := fun hz => (hn x hxU).2 (by rw [hz, map_zero])
  have hx' : Order.coheight xU = 1 := by
    rw [← coheight_eq_of_isOpenImmersion U.ι]
    exact hx
  obtain ⟨z₀, hz₀, he₀⟩ := exists_chart_face_point p U xU 0
  obtain ⟨z₁, hz₁, he₁⟩ := exists_chart_face_point p U xU 1
  constructor
  · have h := originalOrderCycle_zero_chart_coefficient p v f U a b ha hb hab xU hx' z₀ hz₀
    rwa [he₀] at h
  · have h := originalOrderCycle_one_chart_coefficient p v f U a b ha hb hab xU hx' z₁ hz₁
    rwa [he₁] at h

end AlgebraicGeometry.PrincipalFamilyUnitOpen
