/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineSchemeSectionNormCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineGenericRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.OpenImmersion

/-!
# Original chart zero cycles and the global generic ratio norm

One actual affine chart and one canonical spectrum frame identify the pushed
original zero cycles with the order of the original global ratio norm. The
fraction relation, scalar regularity and cycle comparison are all derived.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioChartCycle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme

attribute [local instance] Scheme.functionField_openImmersion_dominant
  Scheme.functionField_nonempty_preimage

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

private theorem fromSpec_functionFieldMap_germ
    {T : Scheme.{u}} [IsIntegral T] (U : T.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (a : Γ(T, U)) :
    Scheme.functionFieldMap hU.fromSpec (T.germToFunctionField U a) =
      _root_.PrimeSpectrum.FiniteFiber.affineFunction Γ(T, U) a := by
  have h := Scheme.functionFieldMap_germ_open hU.fromSpec U
  rw [hU.fromSpec_app_self, Category.assoc] at h
  have hg : (Spec Γ(T, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
      (Spec Γ(T, U)).germToFunctionField (hU.fromSpec ⁻¹ᵁ U) =
      (Spec Γ(T, U)).germToFunctionField ⊤ := by
    exact (Spec Γ(T, U)).presheaf.germ_res _ _ _
  rw [hg] at h
  exact ConcreteCategory.congr_hom h a

variable {C T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  (f : C ⟶ T) [IsFinite f] (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
  [IsNoetherianRing Γ(T, U)] [IsIntegrallyClosed Γ(T, U)]

local instance : IsAffine (Limits.pullback f hU.fromSpec) :=
  isAffine_of_isAffineHom (Limits.pullback.snd f hU.fromSpec)

local instance : IsNoetherian (Limits.pullback f hU.fromSpec) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Limits.pullback.snd f hU.fromSpec)

local instance {X : Scheme.{u}} [IsNoetherian X]
    {M : X.Modules} (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    IsNoetherian (Scheme.Modules.Hom.zeroScheme φ) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion φ)

/-- On the original finite-free affine chart, the original pulled zero cycles
have the order of the canonical global ratio norm at every original target point. -/
theorem genericRatio_chart_zeroCycle_coefficient
    (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (e : (pullbackLineBundle (Limits.pullback f hU.fromSpec).isoSpec.inv
      (pullbackLineBundle (Limits.pullback.fst f hU.fromSpec) L)).val.over ⊤ ≅
      SheafOfModules.unit ((Spec Γ(Limits.pullback f hU.fromSpec, ⊤)).ringCatSheaf.over ⊤)) :
    let : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (Limits.pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤)]
      (x : Spec Γ(T, U)),
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (Limits.pullback.snd f
          hU.fromSpec)
        (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion
              (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) φ))
            (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
              (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) φ))) -
          _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion
              (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) ψ))
            (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
              (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) ψ))))) x =
        T.ord (Scheme.genericFiberLineRatioNorm f L φ ψ) (hU.fromSpec x) := by
  let D := Limits.pullback f hU.fromSpec
  let j := Limits.pullback.fst f hU.fromSpec
  let p := Limits.pullback.snd f hU.fromSpec
  let L' := pullbackLineBundle j L
  let φ' := pullbackUnitMap j φ
  let ψ' := pullbackUnitMap j ψ
  let : Mono φ' := by dsimp [φ', pullbackUnitMap]; infer_instance
  let : Mono ψ' := by dsimp [ψ', pullbackUnitMap]; infer_instance
  let : Algebra Γ(T, U) Γ(D, ⊤) := (FiniteSchemeNormBaseChange.scalarMap p).toAlgebra
  dsimp only
  intro hfree x
  let : Module.Free Γ(T, U) Γ(D, ⊤) := hfree
  let a := affineFrameScalar Γ(D, ⊤) (pullbackLineBundle D.isoSpec.inv L')
    (pullbackUnitMap D.isoSpec.inv φ') e
  let b := affineFrameScalar Γ(D, ⊤) (pullbackLineBundle D.isoSpec.inv L')
    (pullbackUnitMap D.isoSpec.inv ψ') e
  let : Mono (pullbackUnitMap D.isoSpec.inv ψ') := by
    dsimp [pullbackUnitMap]; infer_instance
  have hb : b ∈ nonZeroDivisors _ :=
    affineFrameScalar_mem_nonZeroDivisors Γ(D, ⊤) (pullbackLineBundle D.isoSpec.inv L')
      (pullbackUnitMap D.isoSpec.inv ψ') e
  have hr := _root_.AlgebraicGeometry.Scheme.genericFiberLineRatioUnit_mul_affineFrame f j
    (Scheme.genericFiberChartProjection f U hU)
    (Scheme.genericFiberChartProjection_fst f U hU) L φ ψ e
  have hn := Scheme.genericFiber_norm_eq_chart_norm_ratio f U hU
    (Scheme.genericFiberLineRatioUnit f L φ ψ).val a b hb hr
  change Scheme.genericFiberLineRatioNorm f L φ ψ =
    T.germToFunctionField U (Algebra.norm Γ(T, U) a) /
      T.germToFunctionField U (Algebra.norm Γ(T, U) b) at hn
  have hf : Scheme.functionFieldMap hU.fromSpec (Scheme.genericFiberLineRatioNorm f L φ ψ) =
      _root_.PrimeSpectrum.FiniteFiber.affineFunction Γ(T, U) (Algebra.norm Γ(T, U) a) /
        _root_.PrimeSpectrum.FiniteFiber.affineFunction Γ(T, U) (Algebra.norm Γ(T, U) b) := by
    rw [hn, map_div₀, fromSpec_functionFieldMap_germ U hU,
      fromSpec_functionFieldMap_germ U hU]
  have hc := congrArg (fun c => c x)
    (_root_.AlgebraicGeometry.Scheme.residuePushforward_affineScheme_section_norm_ratio Γ(T, U) p L'
        φ' ψ' e)
  rw [_root_.PrimeSpectrum.FiniteFiber.affinePrincipalOrderCycle_apply, ← hf,
    Scheme.ord_functionFieldMap_of_isOpenImmersion] at hc
  exact hc

end AlgebraicGeometry.Scheme
