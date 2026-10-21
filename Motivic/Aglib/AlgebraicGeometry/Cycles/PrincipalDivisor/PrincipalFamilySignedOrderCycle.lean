/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.PrincipalSectionOrderCycle
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyLocalFraction

/-!
# The original principal family has the signed numerator/denominator cycle

On the prescribed original chart, the actual rational family pulls back to
its literal polynomial numerator divided by its constant denominator. The
whole nonreduced zero cycles give its native order coefficients at every point.
No cycle comparison is supplied as a premise.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.PrincipalFamilySignedOrderCycle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartSpecialization`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u

namespace AlgebraicGeometry.Scheme

/-- The nonempty open instance used in this module. -/
local instance principalFamilySignedOrderCycleNonempty1
    {P : Scheme.{u}} [IsIntegral P] : Nonempty (⊤ : P.Opens) :=
  ⟨⟨genericPoint P, TopologicalSpace.Opens.mem_top (genericPoint P)⟩⟩

/-- The literal signed zero-divisor cycle has the native fraction's order
coefficient, including empty supports and nonreduced zero schemes. -/
theorem signed_section_fundamentalCoefficient_eq_ord
    {k : Type u} [Field k] {P : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
    (p : P ⟶ Spec (.of k)) (n d : Γ(P, ⊤)) (hn : n ≠ 0) (hd : d ≠ 0) (x : P) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion
          (Scheme.sectionToAffineLine p n) 0)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (Scheme.sectionToAffineLine p n)
              0)) -
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion
            (Scheme.sectionToAffineLine p d) 0)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (Scheme.sectionToAffineLine p d)
              0))) x =
      P.ord (P.germToFunctionField ⊤ n / P.germToFunctionField ⊤ d) x := by
  rw [map_sub, Finsupp.sub_apply,
      _root_.AlgebraicGeometry.Scheme.section_zero_fundamentalCoefficient_eq_ord p n hn,
    _root_.AlgebraicGeometry.Scheme.section_zero_fundamentalCoefficient_eq_ord p d hd]
  have hn' := (map_ne_zero_iff _ (P.germToFunctionField_injective ⊤)).mpr hn
  have hd' := (map_ne_zero_iff _ (P.germToFunctionField_injective ⊤)).mpr hd
  have h := P.ord_add_ord_ratio _ _ hd' hn' x
  omega

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

attribute [local instance] Scheme.functionField_nonempty_preimage
  Scheme.functionField_openImmersion_dominant Scheme.nonempty_image_open

/-- The nonempty open instance used in this module. -/
local instance principalFamilySignedOrderCycleNonempty2
    {P : Scheme.{u}} [IsIntegral P] : Nonempty (⊤ : P.Opens) :=
  ⟨⟨genericPoint P, TopologicalSpace.Opens.mem_top (genericPoint P)⟩⟩

/-- The two actual zero schemes on the prescribed chart recover the original
ambient H's pulled-back order, not the order of a separately chosen family. -/
theorem ambientRationalFunction_chart_signed_cycle
    {k : Type u} [Field k] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) (v : W ⟶ C) [IsOpenImmersion v]
    [IsIntegral C] [IsIntegral W] [IsIntegral (parameterSpace p)]
    [IsIntegral (parameterSpace (v ≫ p))]
    (f : Γ(W, ⊤)) [Nonempty (unitOpen (v ≫ p) f)]
    [Nonempty (ambientUnitOpen p v f)]
    (U : C.Opens) [Nonempty U] [IsIntegral (parameterSpace (U.ι ≫ p))]
    [IsNoetherian (parameterSpace (U.ι ≫ p))]
    (a b : Γ(C, U)) (hb : b ≠ 0)
    (hab : C.germToFunctionField U a / C.germToFunctionField U b =
      C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f))
    (x : parameterSpace (U.ι ≫ p)) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
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
            (U.topIso.inv b)) 0))) x =
      (parameterSpace (U.ι ≫ p)).ord
        (Scheme.functionFieldMap (lineMap p U.ι) (ambientRationalFunction p v f)) x := by
  have hb' : U.topIso.inv b ≠ 0 := by
    intro h
    apply hb
    simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero]
      using congrArg U.topIso.hom h
  have hn : PrincipalFamilyEndpointCuts.numerator (U.ι ≫ p)
      (U.topIso.inv a) (U.topIso.inv b) ≠ 0 := by
    intro h
    apply hb'
    have he := congrArg ((endpoint (U.ι ≫ p) 0).appTop) h
    simpa only [PrincipalFamilyEndpointCuts.numerator_zero, map_zero] using he
  have hd : PrincipalFamilyEndpointCuts.denominator (U.ι ≫ p) (U.topIso.inv b) ≠ 0 := by
    intro h
    apply hb'
    have he := congrArg ((endpoint (U.ι ≫ p) 0).appTop) h
    simpa only [PrincipalFamilyEndpointCuts.denominator_endpoint, map_zero] using he
  rw [ambientRationalFunction_chart_fraction (p := p) (v := v) f U a b hb hab]
  exact _root_.AlgebraicGeometry.Scheme.signed_section_fundamentalCoefficient_eq_ord
    (projection (U.ι ≫ p) ≫ U.ι ≫ p) _ _ hn hd x

end AlgebraicGeometry.PrincipalFamilyUnitOpen
