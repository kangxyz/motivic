/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.StaticBoundaryPencilAction
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroLocus.OpenRestriction
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberRetainedLift
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.SectionZeroCycleOpenBaseChange


/-!
# Static boundary correspondences retain the original global zero cycle

The whole original zero scheme is restricted to the actual retained open and
mapped to the original source-target product. This dictionary preserves all
nilpotent lengths and permits signed norm comparisons before applying transfers.
-/

open _root_.AlgebraicGeometry.Scheme.IntegralCycle
  (openImmersionRestriction_finitePushforward_lift)

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace Motivic.Cor

/-- The original boundary-functional correspondence is the retained pushforward
of its original global whole zero cycle, not a chosen divisor presentation. -/
theorem toPoints_boundaryFunctional
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {C B U : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ X.left) [IsProper q]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle C)
    (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
    (g : U ⟶ Y.left) (hbase : (j ≫ q) ≫ X.hom = g ≫ Y.hom) :
    let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType q
    let : IsNoetherian (Hom.zeroScheme a) :=
        _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion a)
    FiniteCorrespondence.toPoints (boundaryFunctional X Y i q j L a hcover g hbase) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (pullback.lift (j ≫ q) g
          hbase)
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion a)
            (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a))))) := by
  let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType q
  let : IsNoetherian U := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_openImmersion j
  let : IsNoetherian (Hom.zeroScheme a) :=
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion a)
  let a' := Hom.pullbackToUnit a j
  let : IsNoetherian (Hom.zeroScheme a') :=
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion a')
  let := lineBundle_isLocallyFree C L
  have hz : Set.range (Hom.zeroInclusion a) ⊆ Set.range j := by
    let : IsIso (Hom.pullbackToUnit a i) := by unfold Hom.pullbackToUnit; infer_instance
    let : IsEmpty (pullback i (Hom.zeroInclusion a) : Scheme.{u}) :=
      Hom.isEmpty_pullback_zeroInclusion a i
    rintro x ⟨z, rfl⟩
    rcases hcover (Hom.zeroInclusion a z) with hx | hx
    · exact hx
    · have hz' : z ∈ Set.range (pullback.snd i (Hom.zeroInclusion a)) := by
        rw [Scheme.Pullback.range_snd]
        exact hx
      obtain ⟨w, _⟩ := hz'
      exact isEmptyElim w
  let e := Hom.zeroRestrictionIso a j hz
  let l := e.inv ≫ Hom.zeroInclusion a'
  have hl : l ≫ j = Hom.zeroInclusion a := by
    dsimp only [l]
    rw [Category.assoc, ← Hom.zeroRestrictionIso_hom_inclusion a j hz,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let : IsFinite (l ≫ j) := by rw [hl]; infer_instance
  have hc : _root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a))) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion a')
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a')) := by
    have hr := openImmersionRestriction_finitePushforward_lift j l
      (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a))
    have hr' : _root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion a)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a))) =
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward l
            (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a)) := by
      simpa only [hl] using hr
    rw [hr']
    apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
    rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply]
    change _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (e.inv ≫
        Hom.zeroInclusion a') _ = _
    rw [_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
        AddMonoidHom.comp_apply,
      _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
          _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
      _root_.AlgebraicGeometry.Scheme.residuePushforward_fundamentalPointCycle]
  have hf := boundaryFunctional_finite_flat X i q j L a hcover
  let : IsFinite (Hom.zeroInclusion a' ≫ j ≫ q) := hf.1
  let : Flat (Hom.zeroInclusion a' ≫ j ≫ q) := hf.2
  dsimp only
  rw [hc]
  unfold boundaryFunctional FiniteCorrespondence.toPoints
  dsimp only
  rw [AddMonoidHom.comp_apply]
  rw [toIntegralCycle_ofFiniteFlatSpan,
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply]
  have hm : pullback.lift (Hom.zeroInclusion a' ≫ j ≫ q)
      (Hom.zeroInclusion a' ≫ g)
      (by simpa only [Category.assoc] using
        congrArg (Hom.zeroInclusion a' ≫ ·) hbase) =
      Hom.zeroInclusion a' ≫ pullback.lift (j ≫ q) g hbase := by
    apply pullback.hom_ext <;> simp
  erw [hm, _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
      AddMonoidHom.comp_apply]

end Motivic.Cor
