/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.PointCycle


/-! # Norm pushforward of original boundary zeros without an ambient pullback

The full zero scheme lies in the retained source by the original boundary unit.
Its exact open restriction is therefore an isomorphism, even if the retained
source is strictly smaller than the full inverse image of the target open.
All multiplicities and nilpotents are retained. Only actual map commutation is
required, not smoothness or equality of the omitted inverse-image points.
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

/-- The original whole-zero norm dictionary requires only a commuting retained
square: boundary-unit support constructs the exact zero-scheme lifts. -/
theorem toPoints_boundaryFunctional_of_comm
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {T C V U B : Scheme.{u}} (q : T ⟶ X.left) [IsProper q]
    (f : C ⟶ T) [IsFinite f] (j : V ⟶ T) [IsOpenImmersion j]
    (i : B ⟶ C) (l : U ⟶ C) [IsOpenImmersion l] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (l ≫ (f ≫ q))]
    (w : U ⟶ V) (hw : l ≫ f = w ≫ j)
    (L : LineBundle C) (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (hc : ∀ x : C, x ∈ Set.range l ∨ x ∈ Set.range i)
    (g : V ⟶ Y.left) (hb : (j ≫ q) ≫ X.hom = g ≫ Y.hom) :
    let : IsNoetherian T := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType q
    let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
    let : IsNoetherian (Hom.zeroScheme a) :=
        _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Hom.zeroInclusion a)
    let hbase : (l ≫ (f ≫ q)) ≫ X.hom = (w ≫ g) ≫ Y.hom := by
      simpa only [← Category.assoc, hw] using congrArg (w ≫ ·) hb
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
  let := lineBundle_isLocallyFree C L
  have hz : Set.range (Hom.zeroInclusion a) ⊆ Set.range l := by
    let : IsIso (Hom.pullbackToUnit a i) := by unfold Hom.pullbackToUnit; infer_instance
    let : IsEmpty (pullback i (Hom.zeroInclusion a) : Scheme.{u}) :=
      Hom.isEmpty_pullback_zeroInclusion a i
    rintro x ⟨z, rfl⟩
    rcases hc (Hom.zeroInclusion a z) with hx | hx
    · exact hx
    · have hz' : z ∈ Set.range (pullback.snd i (Hom.zeroInclusion a)) := by
        rw [Scheme.Pullback.range_snd]
        exact hx
      obtain ⟨y, _⟩ := hz'
      exact isEmptyElim y
  let e := Hom.zeroRestrictionIso a l hz
  let z := e.inv ≫ Hom.zeroInclusion (Hom.pullbackToUnit a l)
  have hzmap : z ≫ l = Hom.zeroInclusion a := by
    dsimp only [z]
    rw [Category.assoc, ← Hom.zeroRestrictionIso_hom_inclusion a l hz,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let : IsFinite (z ≫ l) := by rw [hzmap]; infer_instance
  have hzw : (z ≫ w) ≫ j = Hom.zeroInclusion a ≫ f := by
    rw [Category.assoc, ← hw, ← Category.assoc, hzmap]
  let : IsFinite ((z ≫ w) ≫ j) := by rw [hzw]; infer_instance
  let : IsFinite (z ≫ w) := IsFinite.of_comp (z ≫ w) j
  have hs : _root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction l
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a))) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward z
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a)) := by
    simpa only [hzmap] using openImmersionRestriction_finitePushforward_lift
      l z (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a))
  have ht : _root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward f
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (Hom.zeroInclusion a)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a)))) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (z ≫ w)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a)) := by
    have hp := openImmersionRestriction_finitePushforward_lift
      j (z ≫ w) (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Hom.zeroScheme a))
    simpa only [hzw, _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp,
        AddMonoidHom.comp_apply] using hp
  dsimp only
  rw [toPoints_boundaryFunctional]
  have hm : pullback.lift (l ≫ (f ≫ q)) (w ≫ g)
      (by simpa only [← Category.assoc, hw] using congrArg (w ≫ ·) hb) =
      w ≫ pullback.lift (j ≫ q) g hb := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      simpa only [Category.assoc] using congrArg (· ≫ q) hw
    · simp
  rw [hm, _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
      AddMonoidHom.comp_apply, hs, ht,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
        AddMonoidHom.comp_apply]
  simp only [z, _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
      AddMonoidHom.comp_apply]

end Motivic.Cor
