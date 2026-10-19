/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Cycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberRetainedLift


/-!
# Original retained cycles and finite point correspondences

The ordinary correspondence is the residue pushforward of its original retained
cycle. Finiteness is imposed only on each original support, not on the whole
retained source-target morphism. Every coefficient and image collision is kept.
-/

open _root_.AlgebraicGeometry.Scheme.IntegralCycle
  (openImmersionRestriction_finitePushforward_lift)

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FinitePointCycleCorrespondence

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  {C V : Scheme.{u}} [IsNoetherian C]
  (q : C ⟶ X.left) (j : V ⟶ C) [IsOpenImmersion j]
  (c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle C)
  (hr : ∀ x : c.support,
    Set.range (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ⊆ Set.range j)
  (hfinite : ∀ x : c.support,
    IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q))
  (hdominant : ∀ x : c.support,
    Set.range ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q) ∈
      irreducibleComponents X.left)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

omit [AlgebraicGeometry.IsNoetherian C] in
/-- The finite-image generator has the image of the original generic point. -/
theorem generator_point_original (x : c.support) :
    (generator q j c hr hfinite hdominant g hbase x).point =
      productMap q j c hr g hbase x (genericPoint (supportScheme c x)) := by
  let e := productMap q j c hr g hbase x
  have : IsFinite e := productMap_isFinite q j c hr hfinite g hbase x
  let := _root_.AlgebraicGeometry.Scheme.Hom.isIntegral_finiteImage e
  change e.imageι (genericPoint e.image) = e (genericPoint (supportScheme c x))
  exact _root_.AlgebraicGeometry.Scheme.Hom.imageι_genericPoint e

/-- Original finite point correspondence, with its full residue-degree weights,
is the pushforward of the original open-restricted cycle. -/
theorem toPoints_correspondence_retained_pushforward :
    FiniteCorrespondence.toPoints (f := X.hom) (g := Y.hom)
      (correspondence q j c hr hfinite hdominant g hbase) =
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
      (pullback.lift (j ≫ q) g (by simpa only [Category.assoc] using hbase))
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints c))) := by
  classical
  let r : V ⟶ pullback X.hom Y.hom :=
    pullback.lift (j ≫ q) g (by simpa only [Category.assoc] using hbase)
  have hc : c = ∑ x : c.support, Finsupp.single x.val (c x.val) :=
    c.sum_single.symm.trans
      (Finset.sum_coe_sort c.support (fun x => Finsupp.single x (c x))).symm
  have hsum : _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints c)) =
      ∑ x : c.support, c x.val •
          _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (IsOpenImmersion.lift j
            (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
            x.val).val.subschemeι
          (hr x)) (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
              (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (supportScheme c x))) := by
    conv_lhs => rw [hc]
    simp only [map_sum, _root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints_single]
    apply Finset.sum_congr rfl
    intro x _
    let d := (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι
    let l := IsOpenImmersion.lift j d (hr x)
    have hl : l ≫ j = d := IsOpenImmersion.lift_fac j d (hr x)
    have : IsClosedImmersion (l ≫ j) := by rw [hl]; infer_instance
    have : IsClosedImmersion l := IsClosedImmersion.of_comp l j
    have h := openImmersionRestriction_finitePushforward_lift j l
      (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (supportScheme c x))
    simp only [hl] at h
    have hd : _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward d
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (supportScheme c x)) =
        Finsupp.single (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val)
            1 :=
      _root_.AlgebraicGeometry.Scheme.closedFundamentalCycle_of_isIntegral _
    rw [hd] at h
    have hs : Finsupp.single (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val) (c x.val) =
        c x.val • Finsupp.single
            (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val) (1 : ℤ) :=
            by
      simp
    rw [hs, map_zsmul, map_zsmul, h,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply]
  rw [hsum, map_sum]
  change FiniteCorrespondence.toPoints (∑ x : c.support, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [FiniteCorrespondence.toPoints_single, map_zsmul,
    ← AddMonoidHom.comp_apply, ←
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
    _root_.AlgebraicGeometry.Scheme.fundamentalCycle_of_isIntegral,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_single,
    _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.point_pointClosure,
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_single]
  have he : IsOpenImmersion.lift j
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val).val.subschemeι
          (hr x) ≫ r =
      productMap q j c hr g hbase x := by
    apply pullback.hom_ext
    · simp only [Category.assoc, r, pullback.lift_fst,
        IsOpenImmersion.lift_fac_assoc]
      exact (productMap_fst q j c hr g hbase x).symm
    · simp only [Category.assoc, r, pullback.lift_snd]
      exact (pullback.lift_snd _ _ _).symm
  change Finsupp.single _ _ = c x.val • Finsupp.single _ _
  rw [he, generator_point_original X Y q j c hr hfinite hdominant g hbase x]
  simp

end Motivic.FinitePointCycleCorrespondence
