/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.PrincipalFamilySignedOrderCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.PrincipalOrder
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberOpenRestriction
public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.OpenImmersion

/-!
# The original principal family on its literal numerator/denominator chart

Native open-image transport restricts the unchanged ambient signed order cycle.
Its weighted component specialization is exactly the existing numerator-minus-
denominator face cycle on the original polynomial chart.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartSpecialization`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.`
Module suffix: `PrincipalFamilyChartEndpointCoefficients`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberRetainedLift`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.CartesianOpenPushforward`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u

namespace AlgebraicGeometry.Scheme.IntegralCycle

variable {P Q : Scheme.{u}} (i : Q ⟶ P) [IsOpenImmersion i]

/-- Restriction along the original open immersion uses its canonical open-image iso. -/
def openImmersionRestriction : _root_.AlgebraicGeometry.Scheme.IntegralCycle P →+
    _root_.AlgebraicGeometry.Scheme.IntegralCycle Q :=
  (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward i.isoOpensRange.inv).comp
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction i.opensRange)

/-- Every original point coefficient is unchanged under the literal open map. -/
theorem toPoints_openImmersionRestriction (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle P) (x :
    Q) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints (openImmersionRestriction i c) x =
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c (i x) := by
  rw [openImmersionRestriction, AddMonoidHom.comp_apply,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
        _root_.AlgebraicGeometry.Scheme.residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  have h := Finsupp.mapDomain_apply_of_injective i.isoOpensRange.inv.homeomorph.injective
    (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction i.opensRange c))
        (i.isoOpensRange.hom x)
  change (Finsupp.mapDomain (⇑i.isoOpensRange.inv)
    (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction i.opensRange c)))
    (i.isoOpensRange.inv (i.isoOpensRange.hom x)) = _ at h
  rw [Scheme.hom_inv_apply] at h
  change (Finsupp.mapDomain (⇑i.isoOpensRange.inv)
    (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction i.opensRange c))) x = _
  rw [h, _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openRestriction_apply]
  exact congrArg (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c) (congrArg (fun f : Q ⟶ P
      => f x) i.isoOpensRange_hom_ι)

local instance imageOpenNoetherian [IsNoetherian P] : IsNoetherian i.opensRange.toScheme :=
  { toIsLocallyNoetherian := inferInstance
    toCompactSpace := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (i.opensRange : Set P)) }

/-- The weighted component operation commutes with the original open immersion,
using its actual parameter map rather than an assumed chart comparison. -/
theorem wholeComponentFiber_openImmersionRestriction
    {k : Type u} [Field k] [IsNoetherian P] [IsNoetherian Q]
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle
        P) :
    openImmersionRestriction i (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber f
        a c) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (i ≫ f) a
          (openImmersionRestriction i c) := by
  unfold openImmersionRestriction
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_openRestriction,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_closed_pushforward]
  simp only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]

end AlgebraicGeometry.Scheme.IntegralCycle

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

open PrincipalFamilyEndpointCuts

attribute [local instance] Scheme.functionField_openImmersion_dominant
  Scheme.functionField_nonempty_preimage Scheme.nonempty_image_open

local instance {P : Scheme.{u}} [IsIntegral P] : Nonempty (⊤ : P.Opens) :=
  ⟨⟨genericPoint P, TopologicalSpace.Opens.mem_top (genericPoint P)⟩⟩

variable {k : Type u} [Field k] {C W : Scheme.{u}}
  (p : C ⟶ Spec (.of k)) (v : W ⟶ C) [IsOpenImmersion v]
  [IsIntegral C] [IsIntegral W] [IsIntegral (parameterSpace p)]
  [IsNoetherian (parameterSpace p)] [IsIntegral (parameterSpace (v ≫ p))]
  (f : Γ(W, ⊤)) [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
  (U : C.Opens) [Nonempty U] [IsIntegral (parameterSpace (U.ι ≫ p))]
  [IsNoetherian (parameterSpace (U.ι ≫ p))]
  (a b : Γ(C, U)) (hb : b ≠ 0)
  (hab : C.germToFunctionField U a / C.germToFunctionField U b =
    C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f))

/-- The literal ambient order cycle, with the existing actual unit-open producer. -/
def originalOrderCycle : _root_.AlgebraicGeometry.Scheme.IntegralCycle (parameterSpace p) :=
  _root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints
    (_root_.AlgebraicGeometry.Scheme.principalOrderCycle (ambientUnitOpen p v f) (ambientUnitSection
        p v f)
      (isUnit_ambientUnitSection p v f))

include hb hab in
/-- Restricting the original H cycle to the actual polynomial chart gives the
same whole numerator-minus-denominator divisor cycle, with no supplied cycle equality. -/
theorem originalOrderCycle_chart :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction (lineMap p U.ι)
        (originalOrderCycle p v f) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (fiberInclusion (PrincipalFamilyEndpointCuts.numeratorMap (U.ι ≫ p)
            (U.topIso.inv a) (U.topIso.inv b)) 0)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber
              (PrincipalFamilyEndpointCuts.numeratorMap (U.ι ≫ p)
            (U.topIso.inv a) (U.topIso.inv b)) 0)) -
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (fiberInclusion (PrincipalFamilyEndpointCuts.denominatorMap (U.ι ≫ p)
            (U.topIso.inv b)) 0)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber
              (PrincipalFamilyEndpointCuts.denominatorMap (U.ι ≫ p)
            (U.topIso.inv b)) 0)) := by
  apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
  ext x
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction,
    originalOrderCycle, _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_fromPoints,
    _root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply]
  have h := ambientRationalFunction_chart_signed_cycle p v f U a b hb hab x
  rw [Scheme.ord_functionFieldMap_of_isOpenImmersion] at h
  exact h.symm

include hb hab in
/-- The specialization of the original ambient signed cycle restricts to the
actual weighted N/D face cycles. Nonreduced multiplicities are unchanged. -/
theorem originalOrderCycle_chart_specialization (c : k) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction (lineMap p U.ι)
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (parameterProjection p) c
        (originalOrderCycle p v f)) =
      principalDivisorFaceCycle
          (PrincipalFamilyEndpointCuts.numeratorMap (U.ι ≫ p)
            (U.topIso.inv a) (U.topIso.inv b)) (parameterProjection (U.ι ≫ p)) c -
        principalDivisorFaceCycle
          (PrincipalFamilyEndpointCuts.denominatorMap (U.ι ≫ p) (U.topIso.inv b))
          (parameterProjection (U.ι ≫ p)) c := by
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_openImmersionRestriction,
    originalOrderCycle_chart p v f U a b hb hab]
  have hp : lineMap p U.ι ≫ parameterProjection p = parameterProjection (U.ι ≫ p) := by
    simp only [lineMap, parameterProjection, pullback.map, pullback.lift_snd, Category.comp_id]
  simp only [hp]
  exact _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_signed_principalDivisor _
      _ _ _

end AlgebraicGeometry.PrincipalFamilyUnitOpen
