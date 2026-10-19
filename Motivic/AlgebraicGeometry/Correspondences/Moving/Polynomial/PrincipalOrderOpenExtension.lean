/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyPointCycle
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.RetainedPushforward
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph


/-! # Original principal correspondences under retained-open extension

The same genuine unit representative and its original whole support determine
both correspondences. This allows graph cancellation on the enlarged curve
before returning to the marked complement at the level of correspondences.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.PrincipalOrderCorrespondence

/-- Enlarge the original retained open and postcompose by the original target
map, preserving the same principal representative and all residue weights. -/
theorem correspondence_comp_graph_of_open_extension
    {k : Type u} [Field k] (X Y Z : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {C U V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
    (q : C ⟶ X.left) [IsProper q]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (v : V ⟶ C) [IsOpenImmersion v] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (v ≫ q)]
    (w : U ⟶ V) (hw : w ≫ v = j)
    (W : C.Opens) [Nonempty W]
    (hW : (Set.range j)ᶜ ⊆ (W : Set C))
    (hW' : (Set.range v)ᶜ ⊆ (W : Set C))
    (r : Γ(C, W)) (hr : IsUnit r)
    (g : U ⟶ Y.left) (hb : j ≫ q ≫ X.hom = g ≫ Y.hom)
    (g' : V ⟶ Z.left) (hb' : v ≫ q ≫ X.hom = g' ≫ Z.hom)
    (u : Y ⟶ Z) (hgu : g ≫ u.left = w ≫ g') :
    correspondence q j W hW r hr g hb ≫ (Cor.graphFunctor k).map u =
      correspondence q v W hW' r hr g' hb' := by
  have : IsOpenImmersion (w ≫ v) := by rw [hw]; infer_instance
  have : IsOpenImmersion w := IsOpenImmersion.of_comp _ v
  let c := _root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr
  let d := _root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints c
  have hc : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward w
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j d)) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction v d) := by
    rw [_root_.AlgebraicGeometry.Scheme.residuePushforward_eq_mapDomain_of_surjectiveOnStalks w]
    ext y
    change Finsupp.mapDomain w
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j d)) y = _
    by_cases hy : y ∈ Set.range w
    · obtain ⟨x, rfl⟩ := hy
      rw [Finsupp.mapDomain_apply_of_injective w.isOpenEmbedding.injective,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction]
      exact congrArg (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints d) (congrArg (fun m =>
          m x) hw).symm
    · rw [Finsupp.mapDomain_of_notMem_range _ _ hy,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction,
            _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_fromPoints]
      have hv : v y ∉ Set.range j := by
        rintro ⟨x, hx⟩
        apply hy
        refine ⟨x, v.isOpenEmbedding.injective ?_⟩
        exact (congrArg (fun m => m x) hw).trans hx
      exact (_root_.AlgebraicGeometry.Scheme.principalOrderCycle_eq_zero_on_open W r hr (hW
          hv)).symm
  have hm : pullback.lift (j ≫ q) g (by simpa only [Category.assoc] using hb) ≫
      Cor.graphTargetMap k X u =
      w ≫ pullback.lift (v ≫ q) g' (by simpa only [Category.assoc] using hb') := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Cor.graphTargetMap_fst, pullback.lift_fst]
      simpa only [Category.assoc] using congrArg (· ≫ q) hw.symm
    · simp only [Category.assoc, Cor.graphTargetMap_snd, pullback.lift_snd_assoc,
        pullback.lift_snd, hgu]
  apply FiniteCorrespondence.toPoints_injective
  change _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (FiniteCorrespondence.toIntegralCycle
    (f := X.hom) (g := Z.hom)
    (correspondence q j W hW r hr g hb ≫ (Cor.graphFunctor k).map u)) = _
  rw [Cor.toPoints_comp_graph]
  change _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (Cor.graphTargetMap k
      X u)
    (FiniteCorrespondence.toPoints (correspondence q j W hW r hr g hb)) = _
  rw [correspondence_eq_finitePointCycle, correspondence_eq_finitePointCycle,
    FinitePointCycleCorrespondence.toPoints_correspondence_retained_pushforward,
    FinitePointCycleCorrespondence.toPoints_correspondence_retained_pushforward]
  rw [← AddMonoidHom.comp_apply, ←
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp, hm,
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
        AddMonoidHom.comp_apply, hc]
  rfl

end Motivic.PrincipalOrderCorrespondence
