/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PullbackRatioScalar
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts

/-!
# The canonical global ratio norm in one original chart frame

The numerator and denominator are evaluated on the same original chart generator.
Their generic multiplication relation is proved from the original maps, not
assumed. Only the whole actual chart algebra is required to be free.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartFrameNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme

variable {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
  (L : LineBundle C)
  (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]

/-- The original global generic ratio satisfies the same-section relation on
its actual affine chart, with the original chart projection retained. -/
theorem genericFiberLineRatioUnit_mul_chart_section
    (m : Γ((Modules.pullback (Limits.pullback.fst f hU.fromSpec)).obj L.val, ⊤)) :
    (genericFiberLineRatioUnit f L φ ψ :
        Γ(Limits.pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) *
        (genericFiberChartProjection f U hU).appTop
          (Modules.Hom.app (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) ψ) ⊤ m) =
      (genericFiberChartProjection f U hU).appTop
        (Modules.Hom.app (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) φ) ⊤ m) := by
  have h := pullback_ratio_mul_section (genericFiberChartProjection f U hU)
    (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) φ)
    (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) ψ) m
  rw [genericFiberChartLineRatio_eq f U hU L φ ψ] at h
  exact h

/-- In one original whole-chart frame, the global canonical ratio norm is the
ratio of the two actual scalar norms. Scalar regularity is derived from the
original monic denominator, with no source integrality assumption. -/
theorem genericFiberLineRatioNorm_eq_frame_norm_ratio
    (e : ((Modules.pullback (Limits.pullback.fst f hU.fromSpec)).obj L.val).over ⊤ ≅
      SheafOfModules.unit ((Limits.pullback f hU.fromSpec).ringCatSheaf.over ⊤)) :
    let m := chartGenerator (Limits.pullback f hU.fromSpec)
      ((Modules.pullback (Limits.pullback.fst f hU.fromSpec)).obj L.val) ⊤ e
    let a : Γ(Limits.pullback f hU.fromSpec, ⊤) :=
      Modules.Hom.app (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) φ) ⊤ m
    let b : Γ(Limits.pullback f hU.fromSpec, ⊤) :=
      Modules.Hom.app (pullbackUnitMap (Limits.pullback.fst f hU.fromSpec) ψ) ⊤ m
    let : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (Limits.pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤)],
      genericFiberLineRatioNorm f L φ ψ =
        T.germToFunctionField U (Algebra.norm Γ(T, U) a) /
          T.germToFunctionField U (Algebra.norm Γ(T, U) b) := by
  let j := Limits.pullback.fst f hU.fromSpec
  let L' := pullbackLineBundle j L
  let ψ' := pullbackUnitMap j ψ
  let m := chartGenerator (Limits.pullback f hU.fromSpec) L'.val ⊤ e
  let b : Γ(Limits.pullback f hU.fromSpec, ⊤) := Modules.Hom.app ψ' ⊤ m
  let : Mono ψ' := by dsimp [ψ', pullbackUnitMap]; infer_instance
  have hr := (app_injective_iff_chart_regular L' ψ' ⊤ e ⊤ le_rfl).mp
    (Modules.moduleHom_app_injective ψ' ⊤)
  simp only [homOfLE_refl, op_id] at hr
  have hb : b ∈ nonZeroDivisors _ := by
    rw [mem_nonZeroDivisors_iff_left]
    intro z hz
    apply hr
    change ((Limits.pullback f hU.fromSpec).presheaf.map
        (𝟙 (Opposite.op ⊤))) b * z =
      ((Limits.pullback f hU.fromSpec).presheaf.map (𝟙 (Opposite.op ⊤))) b * 0
    rw [(Limits.pullback f hU.fromSpec).presheaf.map_id]
    change b * z = b * 0
    rw [mul_zero]
    exact hz
  let : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (Limits.pullback.snd f hU.fromSpec)).toAlgebra
  dsimp only
  intro hfree
  let : Module.Free Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) := hfree
  exact genericFiber_norm_eq_chart_norm_ratio f U hU _ _ b hb
    (genericFiberLineRatioUnit_mul_chart_section f U hU L φ ψ m)

end AlgebraicGeometry.Scheme
