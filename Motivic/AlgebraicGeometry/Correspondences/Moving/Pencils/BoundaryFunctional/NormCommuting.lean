/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.NormSupport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormArithmetic
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.RetainedPushforward
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyPointCycle


/-! # Original functional norm comparisons with only retained-map commutation

The actual whole zeros are supported on the retained source by boundary units.
Consequently the retained source need not be the entire finite inverse image
of the target open. The original Cartesian interfaces remain available; these
siblings apply to the genuine compactification of an arbitrary etale cover.
-/

open _root_.AlgebraicGeometry.Scheme
  (residuePushforward_zeroCycles_add_eq_principalOrderCycle_product)

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u
namespace Motivic.Cor

/-- The difference of the two original signed section correspondences is the
principal correspondence of the genuine norm quotient representative. The full
omitted locus is covered by its unit neighborhood, not merely by a generic germ. -/
theorem boundaryFunctional_norm_difference_of_comm
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {T V : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (q : T ⟶ X.left) [IsProper q] (j : V ⟶ T) [IsOpenImmersion j]
    [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (C U B : Fin 2 → Scheme.{u}) (f : ∀ t, C t ⟶ T) [∀ t, IsFinite (f t)]
    (i : ∀ t, B t ⟶ C t) (l : ∀ t, U t ⟶ C t) [∀ t, IsOpenImmersion (l t)]
    [∀ t, (U t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (l t ≫ (f t ≫ q))]
    (w : ∀ t, U t ⟶ V) (hw : ∀ t, l t ≫ f t = w t ≫ j)
    (L : ∀ t, LineBundle (C t))
    (a b : ∀ t, (L t).val ⟶ SheafOfModules.unit (C t).ringCatSheaf)
    [∀ t, Mono (a t)] [∀ t, Mono (b t)]
    [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (a t))]
    [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (b t))]
    (hc : ∀ t (x : C t), x ∈ Set.range (l t) ∨ x ∈ Set.range (i t))
    (hnormal : ∀ (O : T.Opens), IsAffineOpen O → Nonempty O →
      IsIntegrallyClosed Γ(T, O))
    (hfree : ∀ t (x : T), ∃ (O : T.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      (let : Algebra Γ(T, O) Γ(Limits.pullback (f t) hO.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f t) hO.fromSpec)).toAlgebra
       Module.Free Γ(T, O) Γ(Limits.pullback (f t) hO.fromSpec, ⊤)))
    (W : T.Opens) [Nonempty W] (hW : (Set.range j)ᶜ ⊆ (W : Set T))
    (r : Γ(T, W)) (hr : IsUnit r)
    (hg : T.germToFunctionField W r =
      Scheme.genericFiberLineRatioNorm (f 0) (L 0) (a 0) (b 0) /
        Scheme.genericFiberLineRatioNorm (f 1) (L 1) (a 1) (b 1))
    (g : V ⟶ Y.left) (hb : (j ≫ q) ≫ X.hom = g ≫ Y.hom) :
    let hbase := fun t => show (l t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom from
      by simpa only [← Category.assoc, hw t] using congrArg (w t ≫ ·) hb
    let d := fun t =>
      boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (a t) (hc t)
          (w t ≫ g) (hbase t) -
        boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (b t) (hc t)
          (w t ≫ g) (hbase t)
    d 0 - d 1 = PrincipalOrderCorrespondence.correspondence q j W hW r hr g
      (by simpa only [Category.assoc] using hb) := by
  let : ∀ t, IsNoetherian (C t) := fun t =>
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (f t)
  let : ∀ t, IsNoetherian (Hom.zeroScheme (a t)) :=
    fun t => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion (a t))
  let : ∀ t, IsNoetherian (Hom.zeroScheme (b t)) :=
    fun t => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion (b t))
  let hbase := fun t => show (l t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom from
    by simpa only [← Category.assoc, hw t] using congrArg (w t ≫ ·) hb
  let d := fun t =>
    boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (a t) (hc t)
        (w t ≫ g) (hbase t) -
      boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (b t) (hc t)
        (w t ≫ g) (hbase t)
  let z := fun t => _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (f t)
    (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion (a t))
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme (a t))) -
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion (b t))
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme (b t))))
  have hz : z 0 - z 1 = _root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints
      (_root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr) := by
    apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
    simpa only [z, map_sub,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
      _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
          _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_fromPoints] using
      _root_.AlgebraicGeometry.Scheme.residuePushforward_zeroCycles_sub_eq_principalOrderCycle_ratio
        C f hnormal hfree L a b W r hr hg
  let p := pullback.lift (j ≫ q) g hb
  have hd (t : Fin 2) : FiniteCorrespondence.toPoints (d t) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward p
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j (z t))) := by
    dsimp only [d]
    rw [map_sub, toPoints_boundaryFunctional_of_comm X Y q (f t) j
      (i t) (l t) (w t) (hw t) (L t) (a t) (hc t) g hb,
      toPoints_boundaryFunctional_of_comm X Y q (f t) j
        (i t) (l t) (w t) (hw t) (L t) (b t) (hc t) g hb]
    simp only [z, map_sub, p]
  change d 0 - d 1 = _
  apply FiniteCorrespondence.toPoints_injective
  rw [map_sub, hd 0, hd 1,
    PrincipalOrderCorrespondence.correspondence_eq_finitePointCycle,
    FinitePointCycleCorrespondence.toPoints_correspondence_retained_pushforward]
  rw [← map_sub, ← map_sub, ← map_sub, hz]

/-- The sum of the two original signed section correspondences is the
principal correspondence of the genuine norm product representative. The full
omitted locus is covered by its unit neighborhood, not merely by a generic germ. -/
theorem boundaryFunctional_norm_sum_of_comm
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {T V : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (q : T ⟶ X.left) [IsProper q] (j : V ⟶ T) [IsOpenImmersion j]
    [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (C U B : Fin 2 → Scheme.{u}) (f : ∀ t, C t ⟶ T) [∀ t, IsFinite (f t)]
    (i : ∀ t, B t ⟶ C t) (l : ∀ t, U t ⟶ C t) [∀ t, IsOpenImmersion (l t)]
    [∀ t, (U t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (l t ≫ (f t ≫ q))]
    (w : ∀ t, U t ⟶ V) (hw : ∀ t, l t ≫ f t = w t ≫ j)
    (L : ∀ t, LineBundle (C t))
    (a b : ∀ t, (L t).val ⟶ SheafOfModules.unit (C t).ringCatSheaf)
    [∀ t, Mono (a t)] [∀ t, Mono (b t)]
    [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (a t))]
    [∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (b t))]
    (hc : ∀ t (x : C t), x ∈ Set.range (l t) ∨ x ∈ Set.range (i t))
    (hnormal : ∀ (O : T.Opens), IsAffineOpen O → Nonempty O →
      IsIntegrallyClosed Γ(T, O))
    (hfree : ∀ t (x : T), ∃ (O : T.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      (let : Algebra Γ(T, O) Γ(Limits.pullback (f t) hO.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f t) hO.fromSpec)).toAlgebra
       Module.Free Γ(T, O) Γ(Limits.pullback (f t) hO.fromSpec, ⊤)))
    (W : T.Opens) [Nonempty W] (hW : (Set.range j)ᶜ ⊆ (W : Set T))
    (r : Γ(T, W)) (hr : IsUnit r)
    (hg : T.germToFunctionField W r =
      Scheme.genericFiberLineRatioNorm (f 0) (L 0) (a 0) (b 0) *
        Scheme.genericFiberLineRatioNorm (f 1) (L 1) (a 1) (b 1))
    (g : V ⟶ Y.left) (hb : (j ≫ q) ≫ X.hom = g ≫ Y.hom) :
    let hbase := fun t => show (l t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom from
      by simpa only [← Category.assoc, hw t] using congrArg (w t ≫ ·) hb
    let d := fun t =>
      boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (a t) (hc t)
          (w t ≫ g) (hbase t) -
        boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (b t) (hc t)
          (w t ≫ g) (hbase t)
    d 0 + d 1 = PrincipalOrderCorrespondence.correspondence q j W hW r hr g
      (by simpa only [Category.assoc] using hb) := by
  let : ∀ t, IsNoetherian (C t) := fun t =>
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (f t)
  let : ∀ t, IsNoetherian (Hom.zeroScheme (a t)) :=
    fun t => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion (a t))
  let : ∀ t, IsNoetherian (Hom.zeroScheme (b t)) :=
    fun t => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion (b t))
  let hbase := fun t => show (l t ≫ (f t ≫ q)) ≫ X.hom = (w t ≫ g) ≫ Y.hom from
    by simpa only [← Category.assoc, hw t] using congrArg (w t ≫ ·) hb
  let d := fun t =>
    boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (a t) (hc t)
        (w t ≫ g) (hbase t) -
      boundaryFunctional X Y (i t) (f t ≫ q) (l t) (L t) (b t) (hc t)
        (w t ≫ g) (hbase t)
  let z := fun t => _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (f t)
    (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion (a t))
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme (a t))) -
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion (b t))
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme (b t))))
  have hz : z 0 + z 1 = _root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints
      (_root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr) := by
    apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
    simpa only [z, map_add, map_sub,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
      _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
          _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_fromPoints] using
      residuePushforward_zeroCycles_add_eq_principalOrderCycle_product
        C f hnormal hfree L a b W r hr hg
  let p := pullback.lift (j ≫ q) g hb
  have hd (t : Fin 2) : FiniteCorrespondence.toPoints (d t) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward p
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j (z t))) := by
    dsimp only [d]
    rw [map_sub, toPoints_boundaryFunctional_of_comm X Y q (f t) j
      (i t) (l t) (w t) (hw t) (L t) (a t) (hc t) g hb,
      toPoints_boundaryFunctional_of_comm X Y q (f t) j
        (i t) (l t) (w t) (hw t) (L t) (b t) (hc t) g hb]
    simp only [z, map_sub, p]
  change d 0 + d 1 = _
  apply FiniteCorrespondence.toPoints_injective
  rw [map_add, hd 0, hd 1,
    PrincipalOrderCorrespondence.correspondence_eq_finitePointCycle,
    FinitePointCycleCorrespondence.toPoints_correspondence_retained_pushforward]
  rw [← map_add, ← map_add, ← map_add, hz]

end Motivic.Cor
