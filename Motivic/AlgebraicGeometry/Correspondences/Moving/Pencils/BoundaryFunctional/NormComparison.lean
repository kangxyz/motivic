/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.PointCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.CartesianOpenPushforward
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormArithmetic
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyPointCycle
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.RetainedPushforward


/-! # Original boundary correspondences and actual generic norm comparisons

Restriction to the original retained open precedes the faithful point-cycle
comparison. No cancellation of an open immersion at a presheaf action is used.
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

/-- The whole original zero correspondence in an actual cartesian retained square
is obtained by restricting its original compact pushforward. -/
theorem toPoints_boundaryFunctional_cartesian
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {T C V U B : Scheme.{u}} (q : T ⟶ X.left) [IsProper q]
    (f : C ⟶ T) [IsFinite f] (j : V ⟶ T) [IsOpenImmersion j]
    (i : B ⟶ C) (l : U ⟶ C) [IsOpenImmersion l] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (l ≫ (f ≫ q))]
    (w : U ⟶ V) (H : IsPullback l w f j)
    (L : LineBundle C) (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (hc : ∀ x : C, x ∈ Set.range l ∨ x ∈ Set.range i)
    (g : V ⟶ Y.left) (hb : (j ≫ q) ≫ X.hom = g ≫ Y.hom) :
    let : IsNoetherian T := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType q
    let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
    let : IsNoetherian (Hom.zeroScheme a) :=
        _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion a)
    let hbase : (l ≫ (f ≫ q)) ≫ X.hom = (w ≫ g) ≫ Y.hom := by
      simpa only [← Category.assoc, H.w] using congrArg (w ≫ ·) hb
    FiniteCorrespondence.toPoints
        (boundaryFunctional X Y i (f ≫ q) l L a hc (w ≫ g) hbase) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (pullback.lift (j ≫ q) g
          hb)
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward f
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion a)
              (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a)))))) := by
  let : IsNoetherian T := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType q
  let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
  let : IsNoetherian (Hom.zeroScheme a) :=
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion a)
  dsimp only
  rw [toPoints_boundaryFunctional]
  have hm : pullback.lift (l ≫ (f ≫ q)) (w ≫ g)
      (by simpa only [← Category.assoc, H.w] using congrArg (w ≫ ·) hb) =
      w ≫ pullback.lift (j ≫ q) g hb := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      simpa only [Category.assoc] using congrArg (· ≫ q) H.w
    · simp
  rw [hm, _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
      AddMonoidHom.comp_apply]
  congr 1
  ext y
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openImmersionRestriction,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply]
  exact _root_.AlgebraicGeometry.Scheme.residuePushforward_openImmersionRestriction_of_isPullback f
      w l j H _ y

/-- The difference of the two original signed section correspondences is the
principal correspondence of the genuine norm quotient representative. The full
omitted locus is covered by its unit neighborhood, not merely by a generic germ. -/
theorem boundaryFunctional_norm_difference
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {T V : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (q : T ⟶ X.left) [IsProper q] (j : V ⟶ T) [IsOpenImmersion j]
    [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (C U B : Fin 2 → Scheme.{u}) (f : ∀ t, C t ⟶ T) [∀ t, IsFinite (f t)]
    (i : ∀ t, B t ⟶ C t) (l : ∀ t, U t ⟶ C t) [∀ t, IsOpenImmersion (l t)]
    [∀ t, (U t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (l t ≫ (f t ≫ q))]
    (w : ∀ t, U t ⟶ V) (H : ∀ t, IsPullback (l t) (w t) (f t) j)
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
      by simpa only [← Category.assoc, (H t).w] using congrArg (w t ≫ ·) hb
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
    by simpa only [← Category.assoc, (H t).w] using congrArg (w t ≫ ·) hb
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
    rw [map_sub, toPoints_boundaryFunctional_cartesian X Y q (f t) j
      (i t) (l t) (w t) (H t) (L t) (a t) (hc t) g hb,
      toPoints_boundaryFunctional_cartesian X Y q (f t) j
        (i t) (l t) (w t) (H t) (L t) (b t) (hc t) g hb]
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
theorem boundaryFunctional_norm_sum
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {T V : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (q : T ⟶ X.left) [IsProper q] (j : V ⟶ T) [IsOpenImmersion j]
    [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (C U B : Fin 2 → Scheme.{u}) (f : ∀ t, C t ⟶ T) [∀ t, IsFinite (f t)]
    (i : ∀ t, B t ⟶ C t) (l : ∀ t, U t ⟶ C t) [∀ t, IsOpenImmersion (l t)]
    [∀ t, (U t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (l t ≫ (f t ≫ q))]
    (w : ∀ t, U t ⟶ V) (H : ∀ t, IsPullback (l t) (w t) (f t) j)
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
      by simpa only [← Category.assoc, (H t).w] using congrArg (w t ≫ ·) hb
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
    by simpa only [← Category.assoc, (H t).w] using congrArg (w t ≫ ·) hb
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
    rw [map_sub, toPoints_boundaryFunctional_cartesian X Y q (f t) j
      (i t) (l t) (w t) (H t) (L t) (a t) (hc t) g hb,
      toPoints_boundaryFunctional_cartesian X Y q (f t) j
        (i t) (l t) (w t) (H t) (L t) (b t) (hc t) g hb]
    simp only [z, map_sub, p]
  change d 0 + d 1 = _
  apply FiniteCorrespondence.toPoints_injective
  rw [map_add, hd 0, hd 1,
    PrincipalOrderCorrespondence.correspondence_eq_finitePointCycle,
    FinitePointCycleCorrespondence.toPoints_correspondence_retained_pushforward]
  rw [← map_add, ← map_add, ← map_add, hz]

end Motivic.Cor
