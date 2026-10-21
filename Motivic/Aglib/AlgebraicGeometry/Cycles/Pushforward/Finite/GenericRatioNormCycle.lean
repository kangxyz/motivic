/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioChartCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.SectionZeroCycleOpenBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFreeAffineNeighborhood

/-!
# Global coefficients of the original section-divisor norm

The original zero cycles of two monic maps from the same line bundle are pushed
along the original finite morphism. Their difference has the order of the
canonical generic ratio norm at every target point. Target normality is expressed
by integrally closed sections on nonempty affine opens. The geometric local
finite-free chart hypothesis remains explicit; no global freeness, source
integrality, chosen local frame family or cycle comparison is assumed.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormCycle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormArithmetic`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.RelativeAffineLineGraphNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.FiniteSchemeNormBaseChange

universe u
namespace AlgebraicGeometry.Scheme

variable {C T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
  (f : C ⟶ T) [IsFinite f]

/-- The Noetherian instance used in this module. -/
local instance genericRatioNormCycleNoetherian {X : Scheme.{u}} [IsNoetherian X]
    {M : X.Modules} (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    IsNoetherian (Scheme.Modules.Hom.zeroScheme φ) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion φ)

/-- The actual global pushed difference of whole zero cycles equals the order
of the canonical generic norm, coefficient by coefficient. The only cover input
is geometric coordinate-module freeness on original affine target neighborhoods. -/
theorem residuePushforward_zeroCycle_sub_eq_ord_genericRatioNorm
    (hnormal : ∀ (U : T.Opens), IsAffineOpen U → Nonempty U →
      IsIntegrallyClosed Γ(T, U))
    (hfree : ∀ x : T, ∃ (U : T.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
       Module.Free Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤)))
    (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (x : T) :
    let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
    (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (Scheme.Modules.Hom.zeroInclusion φ)
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme φ))
              -
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion ψ)
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
              ψ)))) x =
      T.ord (Scheme.genericFiberLineRatioNorm f L φ ψ) x := by
  let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
  dsimp only
  obtain ⟨U, hU, hxU, hfU⟩ := hfree x
  let : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
    (scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  let : Module.Free Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) := hfU
  obtain ⟨V, hV, hxV, _, ⟨e⟩, hfV⟩ :=
    exists_affine_frame_of_finite_free f U hU L x hxU
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let : IsNoetherianRing Γ(T, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : IsIntegrallyClosed Γ(T, V) := hnormal V hV inferInstance
  let D := Limits.pullback f hV.fromSpec
  let j := pullback.fst f hV.fromSpec
  let p := pullback.snd f hV.fromSpec
  let : IsAffine D := isAffine_of_isAffineHom p
  let : IsNoetherian D := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType p
  let : Algebra Γ(T, V) Γ(D, ⊤) := (scalarMap p).toAlgebra
  let : Module.Free Γ(T, V) Γ(D, ⊤) := hfV
  let eSpec := (Scheme.Modules.pullback D.isoSpec.inv).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso D.isoSpec.inv
  let eTop := (SheafOfModules.overFunctor (Spec Γ(D, ⊤)).ringCatSheaf ⊤).mapIso eSpec
  obtain ⟨y, hy⟩ : ∃ y, hV.fromSpec y = x := by
    have : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    exact this
  have h := _root_.AlgebraicGeometry.Scheme.genericRatio_chart_zeroCycle_coefficient f V hV L φ ψ
      eTop y
  let : L.val.IsLocallyFree := lineBundle_isLocallyFree C L
  have hφ := _root_.AlgebraicGeometry.Scheme.residuePushforward_zeroScheme_openBaseChange f
      hV.fromSpec φ y
  have hψ := _root_.AlgebraicGeometry.Scheme.residuePushforward_zeroScheme_openBaseChange f
      hV.fromSpec ψ y
  rw [map_sub, Finsupp.sub_apply] at h ⊢
  erw [hφ, hψ] at h
  simpa only [hy] using h

/-- Package the coefficient identity using any actual unit representative of the
canonical norm. In particular, a separately produced full-boundary representative
is retained unchanged; no arbitrary replacement neighborhood is selected. -/
theorem residuePushforward_zeroCycle_sub_eq_principalOrderCycle
    (hnormal : ∀ (U : T.Opens), IsAffineOpen U → Nonempty U →
      IsIntegrallyClosed Γ(T, U))
    (hfree : ∀ x : T, ∃ (U : T.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
       Module.Free Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤)))
    (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (W : T.Opens) [Nonempty W] (h : Γ(T, W)) (hh : IsUnit h)
    (hg : T.germToFunctionField W h = Scheme.genericFiberLineRatioNorm f L φ ψ) :
    let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (Scheme.Modules.Hom.zeroInclusion φ)
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme φ))
              -
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion ψ)
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme ψ)))
              =
      _root_.AlgebraicGeometry.Scheme.principalOrderCycle W h hh := by
  let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
  dsimp only
  ext x
  rw [_root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply, hg]
  exact residuePushforward_zeroCycle_sub_eq_ord_genericRatioNorm f hnormal hfree L φ ψ x

end AlgebraicGeometry.Scheme
