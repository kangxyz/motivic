/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartSpecialization

/-!
# The whole signed support sum on the prescribed retained open

Open restriction cancels the original open inclusion in finite support maps.
The residue field degree of that inclusion is one by its actual stalk iso.
Applied to each whole support fiber, this identifies the signed component sum
without a flatness premise or an arbitrary nonreduced base-change assertion.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberRetainedLift`.
Incoming project consumers:
`Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.RetainedGraphCycle`,
`Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.RetainedPushforward`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.PointCycle`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.IntegralCycle

variable {C V D : Scheme.{u}} (j : V ⟶ C) [IsOpenImmersion j]

/-- Only the two support maps are finite. The original open inclusion need not be. -/
theorem openImmersionRestriction_finitePushforward_lift (l : D ⟶ V)
    [IsFinite l] [IsFinite (l ≫ j)] (z : _root_.AlgebraicGeometry.Scheme.IntegralCycle D) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (l ≫ j) z) =
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward l z := by
  apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
  ext x
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction,
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
    AddMonoidHom.comp_apply,
        _root_.AlgebraicGeometry.Scheme.residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  exact Finsupp.mapDomain_apply_of_injective j.isOpenEmbedding.injective _ x

/-- The literal whole support-fiber sum equals the open restriction of the
original additive component specialization, including every original signed weight. -/
theorem wholeComponentFiber_retained_sum
    {k : Type u} [Field k] [IsNoetherian C]
    (f : C ⟶ Spec (.of (Polynomial k))) (a : k) (c :
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle C)
    (hr : ∀ x : c.support,
      Set.range (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          x.val).val.subschemeι ⊆ Set.range j) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber f a
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints c))) =
      ∑ x : c.support,
        let d := (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
            x.val).val.subschemeι
        let l := IsOpenImmersion.lift j d (hr x)
        c x.val • _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (fiberInclusion (d ≫ f) a ≫ l)
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (fiber (d ≫ f) a)) := by
  classical
  have hc : c = ∑ x : c.support, Finsupp.single x.val (c x.val) := by
    exact c.sum_single.symm.trans
      (Finset.sum_coe_sort c.support (fun x => Finsupp.single x (c x))).symm
  conv_lhs => rw [hc]
  simp only [map_sum, _root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints_single,
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_single, map_zsmul]
  apply Finset.sum_congr rfl
  intro x _
  let d := (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
      x.val).val.subschemeι
  let l := IsOpenImmersion.lift j d (hr x)
  have hl : l ≫ j = d := IsOpenImmersion.lift_fac j d (hr x)
  have : IsClosedImmersion (l ≫ j) := by rw [hl]; infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l j
  have he : (fiberInclusion (d ≫ f) a ≫ l) ≫ j =
      fiberInclusion (d ≫ f) a ≫ d := by rw [Category.assoc, hl]
  have : IsFinite ((fiberInclusion (d ≫ f) a ≫ l) ≫ j) := by
    rw [he]
    infer_instance
  have h := openImmersionRestriction_finitePushforward_lift j
    (fiberInclusion (d ≫ f) a ≫ l) (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (d ≫ f)
        a))
  simp only [he] at h
  change c x.val • _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
    (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberInclusion (d ≫ f) a ≫ d)
      (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (d ≫ f) a)))) = _
  rw [h, _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
      _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle]

end AlgebraicGeometry.Scheme.IntegralCycle
