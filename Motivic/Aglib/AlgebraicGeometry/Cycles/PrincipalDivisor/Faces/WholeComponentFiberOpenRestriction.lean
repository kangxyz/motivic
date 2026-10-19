/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiber
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.Open

/-!
# Original open restriction of weighted component fibers

The comparison restricts the original closed support and whole scalar fiber.
It does not replace a weighted component specialization by arbitrary pullback
of a nonreduced fundamental cycle.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberOpenRestriction`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartSpecialization`.
-/

open _root_.AlgebraicGeometry.Scheme.IntegralCycle
  (openRestriction_finitePushforward_fundamentalCycle)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.IntegralCycle

local instance open_isNoetherian {P : Scheme.{u}} [IsNoetherian P] (U : P.Opens) :
    IsNoetherian U.toScheme :=
  { toIsLocallyNoetherian := inferInstance
    toCompactSpace := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (U : Set P)) }

variable {k : Type u} [Field k] {P D D' : Scheme.{u}}

/-- The original restricted scalar fiber is the fiber of the original restricted map. -/
def openScalarFiberIso (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (U : P.Opens) :
    ((fiberInclusion f a) ⁻¹ᵁ U).toScheme ≅ fiber (U.ι ≫ f) a :=
  ((isPullback_morphismRestrict (fiberInclusion f a) U).flip.paste_horiz
    (IsPullback.of_hasPullback (endpoint a) f)).isoPullback

@[reassoc]
theorem openScalarFiberIso_hom_inclusion
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (U : P.Opens) :
    (openScalarFiberIso f a U).hom ≫ fiberInclusion (U.ι ≫ f) a =
      (fiberInclusion f a) ∣_ U :=
  ((isPullback_morphismRestrict (fiberInclusion f a) U).flip.paste_horiz
    (IsPullback.of_hasPullback (endpoint a) f)).isoPullback_hom_snd

/-- Open restriction preserves the whole scalar fiber, including all its nilpotents. -/
theorem openRestriction_scalarFiber [IsNoetherian P]
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (U : P.Opens) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion f a)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber f a))) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion (U.ι ≫ f) a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (U.ι ≫ f) a)) := by
  rw [openRestriction_finitePushforward_fundamentalCycle]
  rw [← _root_.AlgebraicGeometry.Scheme.finitePushforward_fundamentalCycle (openScalarFiberIso f a
      U).hom,
    ← AddMonoidHom.comp_apply, ←
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp]
  simp only [openScalarFiberIso_hom_inclusion]

private theorem fiber_pushforward_iso [IsNoetherian D] [IsNoetherian D']
    (i : D ⟶ P) [IsClosedImmersion i] (i' : D' ⟶ P) [IsClosedImmersion i']
    (E : D' ≅ D) (hE : E.hom ≫ i = i')
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion (i ≫ f) a ≫ i)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (i ≫ f) a)) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion (i' ≫ f) a ≫
          i')
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (i' ≫ f) a)) := by
  let F : fiber (i' ≫ f) a ≅ fiber (i ≫ f) a :=
    asIso (pullback.map _ _ _ _ (𝟙 _) E.hom (𝟙 _)
      (by simp) (by simp [← Category.assoc, hE]))
  have hm : F.hom ≫ fiberInclusion (i ≫ f) a ≫ i =
      fiberInclusion (i' ≫ f) a ≫ i' := by
    simp only [F, asIso_hom, fiberInclusion, pullback.map, pullback.lift_snd_assoc,
      Category.assoc, hE]
  rw [← _root_.AlgebraicGeometry.Scheme.finitePushforward_fundamentalCycle F.hom,
    ← AddMonoidHom.comp_apply, ←
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp]
  simp only [hm]

private theorem openRestriction_closed_scalarFiber [IsNoetherian D]
    (i : D ⟶ P) [IsClosedImmersion i]
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (U : P.Opens) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion (i ≫ f) a ≫
          i)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (i ≫ f) a))) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion ((i ∣_ U) ≫
          U.ι ≫ f) a ≫ (i ∣_ U))
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber ((i ∣_ U) ≫ U.ι ≫ f) a)) := by
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_finitePushforward,
    openRestriction_scalarFiber, ← AddMonoidHom.comp_apply, ←
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp]
  have he : (i ∣_ U) ≫ U.ι ≫ f = (i ⁻¹ᵁ U).ι ≫ i ≫ f := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  exact (congrArg (fun t => _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
      (fiberInclusion t a ≫ (i ∣_ U))
    (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber t a))) he).symm

private def supportOpenIso (Z : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme P) (U :
    P.Opens)
    (h : Z.point ∈ U) :
    (Z.openRestriction U h).val.subscheme ≅ (Z.val.subschemeι ⁻¹ᵁ U).toScheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (Z.openRestriction_val U h)) ≪≫
    Z.val.comapIso U.ι ≪≫ (isPullback_morphismRestrict Z.val.subschemeι U).isoPullback.symm

private theorem idealIsoOfEq_hom_inclusion {Q : Scheme.{u}}
    (I J : Q.IdealSheafData) (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι =
      I.subschemeι := by
  cases h
  simp

private theorem supportOpenIso_hom_map (Z : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
    P) (U : P.Opens)
    (h : Z.point ∈ U) :
    (supportOpenIso Z U h).hom ≫ (Z.val.subschemeι ∣_ U) =
      (Z.openRestriction U h).val.subschemeι := by
  simp only [supportOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst, Scheme.IdealSheafData.comapIso_hom_fst]
  exact idealIsoOfEq_hom_inclusion _ _ (Z.openRestriction_val U h)

/-- The original whole-component operation commutes with the literal open
restriction, retaining all original component coefficients and fiber lengths. -/
theorem wholeComponentFiber_openRestriction [IsNoetherian P]
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (U : P.Opens) (c :
        _root_.AlgebraicGeometry.Scheme.IntegralCycle P) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber f a c) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (U.ι ≫ f) a
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U c) := by
  classical
  have hh : (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U).comp
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber f a) =
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (U.ι ≫ f) a).comp
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U) := by
    apply Finsupp.addHom_ext
    intro Z n
    simp only [AddMonoidHom.comp_apply,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_single, map_zsmul]
    by_cases h : Z.point ∈ U
    · rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_single_of_mem U Z h,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_single,
        openRestriction_closed_scalarFiber]
      exact congrArg (fun z => n • z)
        (fiber_pushforward_iso (Z.val.subschemeι ∣_ U)
          (Z.openRestriction U h).val.subschemeι (supportOpenIso Z U h)
          (supportOpenIso_hom_map Z U h) (U.ι ≫ f) a)
    · rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_single_of_not_mem U Z h,
        map_zero]
      have he : IsEmpty (Z.val.subschemeι ⁻¹ᵁ U).toScheme := by
        constructor
        intro x
        have hz := Z.support_preimage_eq_empty_of_point_not_mem U h
        have : (⟨Z.val.subschemeι x.1, x.2⟩ : U.toScheme) ∈
            U.ι ⁻¹' (Z.val.support : Set P) := by
          change Z.val.subschemeι x.1 ∈ Z.val.support
          have hx : Z.val.subschemeι x.1 ∈ Set.range Z.val.subschemeι := ⟨x.1, rfl⟩
          rw [Scheme.IdealSheafData.range_subschemeι] at hx
          convert hx using 1
        rw [hz] at this
        exact this
      let := he
      rw [openRestriction_closed_scalarFiber]
      have hf : IsEmpty (fiber ((Z.val.subschemeι ∣_ U) ≫ U.ι ≫ f) a) :=
        ⟨fun x => isEmptyElim (fiberInclusion ((Z.val.subschemeι ∣_ U) ≫ U.ι ≫ f) a x)⟩
      let := hf
      have hz : _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber ((Z.val.subschemeι ∣_ U) ≫
          U.ι ≫ f) a) = 0 := by
        apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
        ext x
        exact isEmptyElim x
      rw [hz, map_zero, smul_zero]
  exact DFunLike.congr_fun hh c

end AlgebraicGeometry.Scheme.IntegralCycle
