/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.SectionZeroCycleIso
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.Open

/-!
# Original whole zero cycles under arbitrary open base change

The comparison uses the actual cartesian square and the whole zero schemes,
including their nilpotent lengths. No integrality or global trivialization is
assumed. The point-cycle statement even permits arbitrary structure morphisms.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Restriction.SectionZeroCycleOpenBaseChange`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormCycle`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.PointCycle`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme

/-- The source of an open immersion into a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_openImmersion {X Y : Scheme.{u}}
    [IsNoetherian Y] (i : X ⟶ Y) [IsOpenImmersion i] : IsNoetherian X := by
  let : TopologicalSpace.NoetherianSpace X :=
    i.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType i

local instance {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens) :
    IsNoetherian U.toScheme := isNoetherian_of_openImmersion U.ι

private theorem residuePushforward_openSquare_fundamentalPointCycle
    {X X' Y Y' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hc : i ≫ f = g ≫ j) (hr : i.opensRange = f ⁻¹ᵁ j.opensRange) (y : Y') :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward g
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X') y =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X) (j y) := by
  let U := j.opensRange
  let E := IsOpenImmersion.isoOfRangeEq i (f ⁻¹ᵁ U).ι
    (by rw [Scheme.Opens.range_ι]; exact congrArg (fun V : X.Opens => (V : Set X)) hr)
  let D := IsOpenImmersion.isoOfRangeEq j U.ι
    (by rw [Scheme.Opens.range_ι]; rfl)
  have he : E.hom ≫ (f ∣_ U) = g ≫ D.hom := by
    rw [← cancel_mono U.ι]
    simpa [E, D, Category.assoc, morphismRestrict_ι] using hc
  have hfund : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.openRestriction (f ⁻¹ᵁ U)
      (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X) =
          _root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (f ⁻¹ᵁ U).toScheme := by
    simpa only [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openRestriction,
        _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle] using
      congrArg _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_fundamentalCycle (f ⁻¹ᵁ U))
  have h := DFunLike.congr_fun
    (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.openRestriction_residuePushforward f U)
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X)
  simp only [AddMonoidHom.comp_apply] at h
  rw [hfund, ← _root_.AlgebraicGeometry.Scheme.residuePushforward_fundamentalPointCycle E.hom,
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
      (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X)
      (U.ι (D.hom y)) =
    Finsupp.mapDomain D.hom (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward g
      (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X')) (D.hom y) at hy
  rw [Finsupp.mapDomain_apply_of_injective
    (show Function.Injective D.hom from D.hom.homeomorph.injective)] at hy
  have hdmap : D.hom ≫ U.ι = j := by simp [D]
  have hd : U.ι (D.hom y) = j y :=
    congrArg (fun k : Y' ⟶ Y => k y) hdmap
  rw [hd] at hy
  exact hy.symm

/-- Whole fundamental point cycles commute with an actual open cartesian square,
at every target point and with all residue degrees and local lengths retained. -/
theorem residuePushforward_fundamentalPointCycle_openBaseChange
    {X X' Y Y' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    [IsOpenImmersion j] (h : IsPullback i g f j) (y : Y') :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward g
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X') y =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X) (j y) := by
  have hi : i = h.isoPullback.hom ≫ pullback.fst f j := h.isoPullback_hom_fst.symm
  have : IsOpenImmersion i := by rw [hi]; infer_instance
  apply residuePushforward_openSquare_fundamentalPointCycle f g i j h.w _ y
  apply TopologicalSpace.Opens.ext
  change Set.range i = _
  rw [hi, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (show Function.Surjective h.isoPullback.hom from
      h.isoPullback.hom.homeomorph.surjective), Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst j f

/-- Restrict the original module-to-unit map to the literal base change of its
ambient scheme. Its full pushed zero cycle has the original coefficient at the
image point. Quasicoherence suffices; neither a free module nor integrality is required. -/
theorem residuePushforward_zeroScheme_openBaseChange
    {C T T' : Scheme.{u}} [IsNoetherian C]
    (f : C ⟶ T) (j : T' ⟶ T) [IsOpenImmersion j]
    {M : C.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ (show C.Modules from SheafOfModules.unit C.ringCatSheaf))
    (x' : T') :
    let φ' := Scheme.Modules.Hom.pullbackToUnit φ (pullback.fst f j)
    let : IsNoetherian (pullback f j) :=
      isNoetherian_of_openImmersion (pullback.fst f j)
    let : IsNoetherian (Scheme.Modules.Hom.zeroScheme φ') :=
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion
          φ')
    let : IsNoetherian (Scheme.Modules.Hom.zeroScheme φ) :=
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion
          φ)
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (pullback.snd f j)
        (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion φ')
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
              φ'))) x' =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward f
        (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion φ)
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme φ)))
              (j x') := by
  let : IsNoetherian (pullback f j) :=
    isNoetherian_of_openImmersion (pullback.fst f j)
  let : IsNoetherian (Scheme.Modules.Hom.zeroScheme φ) :=
    _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion φ)
  let : IsNoetherian (Scheme.Modules.Hom.zeroScheme
      (Scheme.Modules.Hom.pullbackToUnit φ (pullback.fst f j))) :=
    _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion _)
  dsimp only
  let p := pullback.fst f j
  let φ' := Scheme.Modules.Hom.pullbackToUnit φ p
  let E := Scheme.Modules.Hom.zeroSchemePullbackIso φ p
  let i := E.hom ≫ pullback.snd p (Scheme.Modules.Hom.zeroInclusion φ)
  have hs : IsPullback (Scheme.Modules.Hom.zeroInclusion φ') i p
      (Scheme.Modules.Hom.zeroInclusion φ) :=
    IsPullback.of_iso_pullback
      ⟨by simp [i, E, φ', ← pullback.condition]⟩ E
      (by simp [E, φ']) rfl
  have h := (hs.paste_horiz (IsPullback.of_hasPullback f j).flip).flip
  rw [← AddMonoidHom.comp_apply, ←
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
    ← AddMonoidHom.comp_apply, ←
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp]
  exact residuePushforward_fundamentalPointCycle_openBaseChange _ _ _ _ h x'

end AlgebraicGeometry.Scheme
