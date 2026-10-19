/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberSectionNorm
public import Motivic.Aglib.RingTheory.Norm.GenericUnitFraction

/-!
# Canonical affine-chart comparison for the whole generic norm

The affine chart is the literal pullback along its canonical `fromSpec` map.
Its scalar-extended sections identify with sections of the original global
generic fiber, preserving the original structural and projection maps.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartNorm`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartLineRatio`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry.Scheme

universe u
variable {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]

theorem generic_chart_base_comp :
    Spec.map (T.germToFunctionField U) ≫ hU.fromSpec =
      T.fromSpecStalk (genericPoint T) :=
  hU.fromSpecStalk_eq_fromSpecStalk
    (((genericPoint_spec T).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))

/-- The actual chart generic pullback is canonically the global generic fiber. -/
def genericFiberChartIso :
    pullback (pullback.snd f hU.fromSpec) (Spec.map (T.germToFunctionField U)) ≅
      pullback f (T.fromSpecStalk (genericPoint T)) :=
  pullbackLeftPullbackSndIso f hU.fromSpec (Spec.map (T.germToFunctionField U)) ≪≫
    pullback.congrHom rfl (generic_chart_base_comp U hU)

omit [IsFinite f] in
@[reassoc (attr := simp)]
theorem genericFiberChartIso_hom_snd :
    (genericFiberChartIso f U hU).hom ≫
      pullback.snd f (T.fromSpecStalk (genericPoint T)) =
    pullback.snd (pullback.snd f hU.fromSpec) (Spec.map (T.germToFunctionField U)) := by
  simp [genericFiberChartIso, pullback.congrHom]

omit [IsFinite f] in
@[reassoc (attr := simp)]
theorem genericFiberChartIso_hom_fst :
    (genericFiberChartIso f U hU).hom ≫
      pullback.fst f (T.fromSpecStalk (genericPoint T)) =
    pullback.fst (pullback.snd f hU.fromSpec) (Spec.map (T.germToFunctionField U)) ≫
      pullback.fst f hU.fromSpec := by
  simp [genericFiberChartIso, pullback.congrHom]

/-- The canonical projection from the global generic fiber to the original chart. -/
def genericFiberChartProjection :
    pullback f (T.fromSpecStalk (genericPoint T)) ⟶ pullback f hU.fromSpec :=
  (genericFiberChartIso f U hU).inv ≫
    pullback.fst (pullback.snd f hU.fromSpec) (Spec.map (T.germToFunctionField U))

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extended algebra of the actual finite chart is the algebra of
sections of the whole original generic fiber. -/
def genericFiberChartSectionsEquiv :
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
    T.functionField ⊗[Γ(T, U)] Γ(pullback f hU.fromSpec, ⊤) ≃ₐ[T.functionField]
      Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) := by
  let p := pullback.snd f hU.fromSpec
  let φ := (T.germToFunctionField U).hom
  let G := pullback f (T.fromSpecStalk (genericPoint T))
  let P := pullback p (Spec.map (CommRingCat.ofHom φ))
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap p).toAlgebra
  let : Algebra T.functionField Γ(G, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
  let : Algebra T.functionField Γ(P, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  let : IsAffine (pullback f hU.fromSpec) := isAffine_of_isAffineHom p
  let e : P ≅ G := genericFiberChartIso f U hU
  let ei : Γ(P, ⊤) ≅ Γ(G, ⊤) :=
    { hom := e.inv.appTop
      inv := e.hom.appTop
      hom_inv_id := by
        rw [← Hom.comp_appTop, Iso.hom_inv_id, Hom.id_appTop]
      inv_hom_id := by
        rw [← Hom.comp_appTop, Iso.inv_hom_id, Hom.id_appTop] }
  let ea : Γ(P, ⊤) ≃ₐ[T.functionField] Γ(G, ⊤) :=
    { ei.commRingCatIsoToRingEquiv with
      commutes' a := by
        have hc : CommRingCat.ofHom
            (FiniteSchemeNormBaseChange.scalarMap (pullback.snd p
              (Spec.map (CommRingCat.ofHom φ)))) ≫ ei.hom =
            CommRingCat.ofHom (FiniteSchemeNormBaseChange.scalarMap
              (pullback.snd f (T.fromSpecStalk (genericPoint T)))) := by
          have he : e.inv ≫ pullback.snd p (Spec.map (CommRingCat.ofHom φ)) =
              pullback.snd f (T.fromSpecStalk (genericPoint T)) := by
            apply (cancel_epi e.hom).mp
            rw [Iso.hom_inv_id_assoc]
            exact (genericFiberChartIso_hom_snd f U hU).symm
          have hh := congrArg (fun k : G ⟶ Spec T.functionField =>
            (ΓSpecIso T.functionField).inv ≫ k.appTop) he
          rw [Hom.comp_appTop] at hh
          exact hh
        exact congrArg (fun k : T.functionField ⟶ Γ(G, ⊤) => k.hom a) hc }
  exact (FiniteSchemeNormBaseChange.sectionsTensorEquiv p φ).trans ea

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence uses the original chart projection on each original section. -/
theorem genericFiberChartSectionsEquiv_one_tmul (b : Γ(pullback f hU.fromSpec, ⊤)) :
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
    genericFiberChartSectionsEquiv f U hU ((1 : T.functionField) ⊗ₜ[Γ(T,U)] b) =
      (genericFiberChartProjection f U hU).appTop b := by
  let p := pullback.snd f hU.fromSpec
  let : IsAffine (pullback f hU.fromSpec) := isAffine_of_isAffineHom p
  exact congrArg ((genericFiberChartIso f U hU).inv.appTop)
    (FiniteSchemeNormBaseChange.sectionsTensorEquiv_one_tmul p
      (T.germToFunctionField U).hom b)

/-- The original chart norm pulls back to the norm on the global generic fiber. -/
theorem norm_genericFiberChartProjection (b : Γ(pullback f hU.fromSpec, ⊤)) :
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      Algebra.norm T.functionField ((genericFiberChartProjection f U hU).appTop b) =
        T.germToFunctionField U (Algebra.norm Γ(T, U) b) := by
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
  dsimp only
  intro hfree
  let : Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) := hfree
  let : Module.Finite Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    FiniteSchemeNormBaseChange.sections_finite (pullback.snd f hU.fromSpec)
  rw [← genericFiberChartSectionsEquiv_one_tmul f U hU b]
  exact (Algebra.norm_eq_of_algEquiv (genericFiberChartSectionsEquiv f U hU)
    ((1 : T.functionField) ⊗ₜ[Γ(T, U)] b)).trans (Algebra.norm_one_tmul b)

/-- An actual generic section satisfying the original chart fraction relation
has the ratio of the original norms. Only the denominator must be regular. -/
theorem genericFiber_norm_eq_chart_norm_ratio
    (h : Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤))
    (a b : Γ(pullback f hU.fromSpec, ⊤)) (hb : b ∈ nonZeroDivisors _) :
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      h *
          (genericFiberChartProjection f U hU).appTop b =
        (genericFiberChartProjection f U hU).appTop a →
      Algebra.norm T.functionField h =
        T.germToFunctionField U (Algebra.norm Γ(T, U) a) /
          T.germToFunctionField U (Algebra.norm Γ(T, U) b) := by
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
  dsimp only
  intro hfree he
  let : Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) := hfree
  let : Module.Finite Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    FiniteSchemeNormBaseChange.sections_finite (pullback.snd f hU.fromSpec)
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
  have hn : Algebra.norm Γ(T, U) b ≠ 0 := by
    rw [Algebra.norm_apply, ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
    exact not_not.mpr (LinearMap.ker_eq_bot.mpr
      (isRegular_iff_mem_nonZeroDivisors.mpr hb).1)
  have hd : T.germToFunctionField U (Algebra.norm Γ(T, U) b) ≠ 0 :=
    (map_ne_zero_iff _ (T.germToFunctionField_injective U)).mpr hn
  apply (eq_div_iff hd).mpr
  have hh := congrArg (Algebra.norm T.functionField) he
  rw [map_mul, norm_genericFiberChartProjection f U hU b,
    norm_genericFiberChartProjection f U hU a] at hh
  exact hh

/-- The norm of the same dense-domain section is the ratio of the original
chart norms whenever its actual generic restriction satisfies the displayed
fraction relation. Only the denominator must be regular, not the source ring. -/
theorem genericFiberSectionNorm_eq_chart_norm_ratio [NoetherianSpace C]
    (W : C.Opens) (hW : Dense (W : Set C)) (s : Γ(C, W))
    (a b : Γ(pullback f hU.fromSpec, ⊤)) (hb : b ∈ nonZeroDivisors _) :
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      (genericFiberDenseOpenLift f W hW).appTop (W.topIso.inv s) *
          (genericFiberChartProjection f U hU).appTop b =
        (genericFiberChartProjection f U hU).appTop a →
      genericFiberSectionNorm f W hW s =
        T.germToFunctionField U (Algebra.norm Γ(T, U) a) /
          T.germToFunctionField U (Algebra.norm Γ(T, U) b) := by
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  dsimp only
  intro hfree he
  let : Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) := hfree
  exact genericFiber_norm_eq_chart_norm_ratio f U hU
    ((genericFiberDenseOpenLift f W hW).appTop (W.topIso.inv s)) a b hb he

end AlgebraicGeometry.Scheme
