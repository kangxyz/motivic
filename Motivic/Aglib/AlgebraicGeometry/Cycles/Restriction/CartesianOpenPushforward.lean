/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartSpecialization
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance

/-! # Actual cartesian open restriction of all-point cycle pushforward

The native original open maps are retained through their canonical open-image
isomorphisms. No source integrality, finiteness or cycle equality is assumed.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Restriction.CartesianOpenPushforward`.
Incoming project consumers:
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.NormComparison`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

private theorem residuePushforward_openSquare_cycle
    {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hc : i ≫ f = g ≫ j) (hr : i.opensRange = f ⁻¹ᵁ j.opensRange)
    (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle X) (y : Y') :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward g
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction i c)) y =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c) (j y) := by
  let U := j.opensRange
  let E := IsOpenImmersion.isoOfRangeEq i (f ⁻¹ᵁ U).ι
    (by rw [Scheme.Opens.range_ι]; exact congrArg (fun V : X.Opens => (V : Set X)) hr)
  let D := IsOpenImmersion.isoOfRangeEq j U.ι
    (by rw [Scheme.Opens.range_ι]; rfl)
  have he : E.hom ≫ (f ∣_ U) = g ≫ D.hom := by
    rw [← cancel_mono U.ι]
    simpa [E, D, Category.assoc, morphismRestrict_ι] using hc
  have hfund : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.openRestriction (f ⁻¹ᵁ U)
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c) =
          _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward E.hom
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction i c)) := by
    ext x
    rw [_root_.AlgebraicGeometry.Scheme.residuePushforward_eq_mapDomain_of_surjectiveOnStalks E.hom]
    have hx := Finsupp.mapDomain_apply_of_injective
      (show Function.Injective E.hom from E.hom.homeomorph.injective)
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction i c)) (E.inv x)
    rw [Scheme.inv_hom_apply] at hx
    change _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c x.val =
      Finsupp.mapDomain E.hom
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction i c)) x
    rw [hx, _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction]
    have he : E.inv ≫ i = (f ⁻¹ᵁ U).ι := by simp [E]
    exact congrArg (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c) (congrArg (fun m => m
        x) he).symm
  have h := DFunLike.congr_fun
    (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.openRestriction_residuePushforward f U)
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c)
  simp only [AddMonoidHom.comp_apply] at h
  rw [hfund,
    ← AddMonoidHom.comp_apply (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (f ∣_ U))
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward E.hom),
    ← _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
    he, _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
        AddMonoidHom.comp_apply] at h
  have hy := congrArg (fun c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle U.toScheme => c
      (D.hom y)) h
  rw [_root_.AlgebraicGeometry.Scheme.residuePushforward_eq_mapDomain_of_surjectiveOnStalks D.hom]
      at hy
  change _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c)
      (U.ι (D.hom y)) =
    Finsupp.mapDomain D.hom (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward g
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction i c))) (D.hom y)
          at hy
  rw [Finsupp.mapDomain_apply_of_injective
    (show Function.Injective D.hom from D.hom.homeomorph.injective)] at hy
  have hdmap : D.hom ≫ U.ι = j := by simp [D]
  have hd : U.ι (D.hom y) = j y :=
    congrArg (fun k : Y' ⟶ Y => k y) hdmap
  rw [hd] at hy
  exact hy.symm

/-- All original residue-degree collision sums commute with an actual cartesian
open square, for an arbitrary signed cycle and every original target point. -/
theorem residuePushforward_openImmersionRestriction_of_isPullback
    {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : IsPullback i g f j)
    (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle X) (y : Y') :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward g
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction i c)) y =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c) (j y) := by
  apply residuePushforward_openSquare_cycle f g i j h.w _ c y
  have hi : i = h.isoPullback.hom ≫ pullback.fst f j := h.isoPullback_hom_fst.symm
  apply TopologicalSpace.Opens.ext
  change Set.range i = _
  rw [hi, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (show Function.Surjective h.isoPullback.hom from
      h.isoPullback.hom.homeomorph.surjective), Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst j f

end AlgebraicGeometry.Scheme
