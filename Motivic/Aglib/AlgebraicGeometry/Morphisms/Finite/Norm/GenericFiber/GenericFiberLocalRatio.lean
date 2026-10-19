/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFactorizationRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.IdentityGenericFiberNorm
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairedScalar
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # Native generic norms of the same local section quotient

The local quotient is built from the original numerator and the inverse of its
actual denominator. Its original dual-functional equation identifies the whole
generic-fiber ratio and the native target germ of its chart norm. Only the
target component is integral; no source function field or new frame is used.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLocalRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFunctionalRatio`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

variable {C T W : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (j : W ⟶ C) (q : pullback f (T.fromSpecStalk (genericPoint T)) ⟶ W)
  (hq : q ≫ j = pullback.fst f (T.fromSpecStalk (genericPoint T)))
  (L : LineBundle C)

include hq in
/-- The actual factorized same-line equation identifies the canonical global
ratio endomorphism. Generic denominator invertibility follows from original monicity. -/
theorem genericFiberLineRatioIso_eq_pullback_of_equation
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (θ : SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf)
    (hθ : pullbackUnitMap j ψ ≫ θ = pullbackUnitMap j φ) :
    (genericFiberLineRatioIso f L φ ψ).hom = Hom.unitEndomorphismPullback q θ := by
  have := genericFiberLineMap_factorization_isIso f j q hq L ψ
  have hp : pullbackUnitMap q (pullbackUnitMap j ψ) ≫
      Hom.unitEndomorphismPullback q θ = pullbackUnitMap q (pullbackUnitMap j φ) := by
    have hh := congrArg (pullbackUnitMap q) hθ
    simpa only [pullbackUnitMap, Hom.unitEndomorphismPullback, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_assoc] using hh
  have hc : pullbackUnitMap q (pullbackUnitMap j ψ) ≫
      (genericFiberLineRatioIso f L φ ψ).hom = pullbackUnitMap q (pullbackUnitMap j φ) := by
    rw [genericFiberLineMap_factorization f j q hq L ψ,
      genericFiberLineMap_factorization f j q hq L φ]
    simp only [genericFiberLineRatioIso, Iso.trans_hom, Iso.symm_hom,
      asIso_inv, asIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  exact (cancel_epi (pullbackUnitMap q (pullbackUnitMap j ψ))).mp (hc.trans hp.symm)

include hq in
/-- The canonical original dual-functional ratio is the generic restriction of
this SAME local numerator-over-denominator section quotient. -/
theorem genericFiberLineRatioUnit_eq_sectionQuotient
    (n d : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    [Mono (sectionDualFunctional C L n)] [Mono (sectionDualFunctional C L d)]
    [IsIso (pullbackSectionMap j d)] :
    (genericFiberLineRatioUnit f (dualLineBundle C L)
      (sectionDualFunctional C L n) (sectionDualFunctional C L d) :
        Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) =
    q.appTop (Modules.Hom.app
      (pullbackSectionMap j n ≫ inv (pullbackSectionMap j d)) ⊤ (1 : Γ(W, ⊤))) := by
  have he := genericFiberLineRatioIso_eq_pullback_of_equation f j q hq (dualLineBundle C L)
    (sectionDualFunctional C L n) (sectionDualFunctional C L d)
    (pullbackSectionMap j n ≫ inv (pullbackSectionMap j d))
    (pullback_sectionQuotient_dualFunctional j L n d)
  change Modules.Hom.app (genericFiberLineRatioIso f (dualLineBundle C L)
    (sectionDualFunctional C L n) (sectionDualFunctional C L d)).hom ⊤
      (1 : Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) = _
  rw [he]
  exact Hom.unitEndomorphismPullback_app_one q
    (pullbackSectionMap j n ≫ inv (pullbackSectionMap j d))

omit j q hq in
/-- The original canonical norm is the native germ of the local norm of the
same section quotient on the whole actual finite chart. No rational equality is assumed. -/
theorem genericFiberLineRatioNorm_eq_chart_sectionQuotient
    (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (n d : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    [Mono (sectionDualFunctional C L n)] [Mono (sectionDualFunctional C L d)]
    [IsIso (pullbackSectionMap (pullback.fst f hU.fromSpec) d)] :
    let b : Γ(pullback f hU.fromSpec, ⊤) := Modules.Hom.app
      (pullbackSectionMap (pullback.fst f hU.fromSpec) n ≫
        inv (pullbackSectionMap (pullback.fst f hU.fromSpec) d)) ⊤
          (1 : Γ(pullback f hU.fromSpec, ⊤))
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      genericFiberLineRatioNorm f (dualLineBundle C L)
        (sectionDualFunctional C L n) (sectionDualFunctional C L d) =
      T.germToFunctionField U (Algebra.norm Γ(T, U) b) := by
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  change Algebra.norm T.functionField
    (genericFiberLineRatioUnit f (dualLineBundle C L)
      (sectionDualFunctional C L n) (sectionDualFunctional C L d) :
        Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) = _
  rw [genericFiberLineRatioUnit_eq_sectionQuotient f (pullback.fst f hU.fromSpec)
    (genericFiberChartProjection f U hU) (genericFiberChartProjection_fst f U hU) L n d]
  exact norm_genericFiberChartProjection f U hU _

/-- The identity norm of the original target pair is the native germ of its
same local section quotient, with no separately supplied same-line equation. -/
theorem genericFiberLineRatioNorm_id_eq_sectionQuotient_germ
    {X : Scheme.{u}} [IsIntegral X] (L : LineBundle X)
    (n d : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [Mono (sectionDualFunctional X L n)] [Mono (sectionDualFunctional X L d)]
    (U : X.Opens) [Nonempty U] [IsIso (pullbackSectionMap U.ι d)] :
    let b : Γ(U.toScheme, ⊤) := Modules.Hom.app
      (pullbackSectionMap U.ι n ≫ inv (pullbackSectionMap U.ι d)) ⊤ (1 : Γ(U.toScheme, ⊤))
    genericFiberLineRatioNorm (𝟙 X) (dualLineBundle X L)
      (sectionDualFunctional X L n) (sectionDualFunctional X L d) =
        X.germToFunctionField U (U.topIso.hom b) := by
  dsimp only
  apply genericFiberLineRatioNorm_id_eq_germ (dualLineBundle X L)
    (sectionDualFunctional X L n) (sectionDualFunctional X L d) U
  rw [Iso.hom_inv_id_apply]
  rw [← Modules.unitEnd_eq_unitMul]
  exact pullback_sectionQuotient_dualFunctional U.ι L n d

end AlgebraicGeometry.Scheme
