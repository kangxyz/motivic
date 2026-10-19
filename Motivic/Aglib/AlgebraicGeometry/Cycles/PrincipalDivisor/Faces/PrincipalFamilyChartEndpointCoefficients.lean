/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartSpecialization
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyZeroCoefficient
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyOneCoefficient

/-!
# Original principal-family endpoint coefficients on a prescribed chart

The actual ambient signed order cycle is used throughout. Its zero specialization
vanishes and its one specialization recovers the original rational function's
order at the corresponding codimension-one point. The face point and its
codimension remain explicit here; this is not a global correspondence identity.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartEndpointCoefficients`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyEndpointCoefficients`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

open PrincipalFamilyEndpointCuts

attribute [local instance] Scheme.functionField_openImmersion_dominant
  Scheme.functionField_nonempty_preimage Scheme.nonempty_image_open

local instance {P : Scheme.{u}} [IsIntegral P] : Nonempty (⊤ : P.Opens) :=
  ⟨⟨genericPoint P, TopologicalSpace.Opens.mem_top (genericPoint P)⟩⟩

variable {k : Type u} [Field k] {C W : Scheme.{u}}
  (p : C ⟶ Spec (.of k)) (v : W ⟶ C) [IsOpenImmersion v]
  [IsIntegral C] [IsNoetherian C] [IsIntegral W]
  [IsIntegral (parameterSpace p)] [IsNoetherian (parameterSpace p)]
  [IsIntegral (parameterSpace (v ≫ p))]
  (f : Γ(W, ⊤)) [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
  (U : C.Opens) [Nonempty U] [IsIntegral (parameterSpace (U.ι ≫ p))]
  [IsNoetherian (parameterSpace (U.ι ≫ p))]
  (a b : Γ(C, U)) (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : C.germToFunctionField U a / C.germToFunctionField U b =
    C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f))

local instance chartNoetherian : IsNoetherian U.toScheme :=
  { toIsLocallyNoetherian := inferInstance
    toCompactSpace := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (U : Set C)) }

omit [IsNoetherian C] in
private theorem chart_germ_ne_zero (s : Γ(C, U)) (hs : s ≠ 0) (x : U.toScheme) :
    U.toScheme.presheaf.germ ⊤ x (by trivial) (U.topIso.inv s) ≠ 0 := by
  apply (map_ne_zero_iff _ (germ_injective_of_isIntegral U.toScheme x (by trivial))).mpr
  intro h
  apply hs
  simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero]
    using congrArg U.topIso.hom h

include ha hb hab in
/-- The original ambient family's zero face coefficient vanishes at the actual
chart face point, including mixed and empty divisor support. -/
theorem originalOrderCycle_zero_chart_coefficient
    (x : U.toScheme) (hx : Order.coheight x = 1)
    (q : fiber (parameterProjection (U.ι ≫ p)) 0)
    (hq : fiberInclusion (parameterProjection (U.ι ≫ p)) 0 q = endpoint (U.ι ≫ p) 0 x) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (parameterProjection p) 0
        (originalOrderCycle p v f))
      (lineMap p U.ι (fiberInclusion (parameterProjection (U.ι ≫ p)) 0 q)) = 0 := by
  rw [← _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction (lineMap p
      U.ι),
    originalOrderCycle_chart_specialization p v f U a b hb hab]
  exact original_zero_signed_face_coefficient (U.ι ≫ p) (U.topIso.inv a) (U.topIso.inv b)
    x hx (chart_germ_ne_zero U a ha x) (chart_germ_ne_zero U b hb x) q hq

include ha hb hab in
/-- The one face coefficient is the order of the original rational function,
using the native open-immersion field and stalk maps, not an assumed chart equality. -/
theorem originalOrderCycle_one_chart_coefficient
    (x : U.toScheme) (hx : Order.coheight x = 1)
    (q : fiber (parameterProjection (U.ι ≫ p)) 1)
    (hq : fiberInclusion (parameterProjection (U.ι ≫ p)) 1 q = endpoint (U.ι ≫ p) 1 x) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (parameterProjection p) 1
        (originalOrderCycle p v f))
      (lineMap p U.ι (fiberInclusion (parameterProjection (U.ι ≫ p)) 1 q)) =
      C.ord (C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)) (U.ι x) := by
  rw [← _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction (lineMap p
      U.ι),
    originalOrderCycle_chart_specialization p v f U a b hb hab]
  have h := original_one_signed_face_coefficient (U.ι ≫ p) (U.topIso.inv a) (U.topIso.inv b)
    x hx (chart_germ_ne_zero U a ha x) (chart_germ_ne_zero U b hb x) q hq
  refine h.trans ?_
  have he : U.toScheme.germToFunctionField ⊤ (U.topIso.inv a) /
      U.toScheme.germToFunctionField ⊤ (U.topIso.inv b) =
      Scheme.functionFieldMap U.ι
        (C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)) := by
    rw [← Scheme.functionFieldMap_germ_topIso, ← Scheme.functionFieldMap_germ_topIso,
      ← map_div₀, hab]
  rw [he, Scheme.ord_functionFieldMap_of_isOpenImmersion]

end AlgebraicGeometry.PrincipalFamilyUnitOpen
