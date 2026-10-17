/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCorestriction
public import Motivic.AlgebraicGeometry.Correspondences.FinitePointBaseChange

/-!
# Actual finite-point transfer under scalar extension

The original transferred graph is extended as a whole finite point. Its full
scalar-extended source is retained before decomposing into residue branches.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.DiagonalCorestrictionBaseChange

open PresheafWithTransfers DiagonalCorestriction
open WeightTwoCorestriction (torusMap)

/-- The original base-point and n-torus ambient scheme. -/
abbrev pointAmbient (F : Type u) [Field F] (n : ℕ) : Scheme.{u} :=
  (SmoothSite.product (SmoothSite.base (Spec (.of F))) (SmoothSite.torusPower (.of F) n)).left

variable {n : ℕ}

section Ambient

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The literal whole ambient scalar-extension comparison. -/
def pointAmbientIso :
    (SmoothSite.fieldBaseChange (algebraMap k L)).obj
      (SmoothSite.product (SmoothSite.base (Spec (.of k)))
        (SmoothSite.torusPower (.of k) n)) ≅
    SmoothSite.product (SmoothSite.base (Spec (.of L))) (SmoothSite.torusPower (.of L) n) :=
  SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (SmoothSite.base (Spec (.of k))) (SmoothSite.torusPower (.of k) n) ≪≫
    SmoothSite.productIso
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) n)

/-- The old ambient projection, retaining the original coefficient map. -/
def pointAmbientProjection : pointAmbient L n ⟶ pointAmbient k n :=
  (pointAmbientIso (k := k) (L := L)).inv.left ≫
    pullback.fst (SmoothSite.product (SmoothSite.base (Spec (.of k)))
        (SmoothSite.torusPower (.of k) n)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- The new base projection is exactly the other projection of the whole pullback. -/
@[reassoc (attr := simp)]
theorem pointAmbientIso_inv_base :
    (pointAmbientIso (k := k) (L := L)).inv.left ≫
      pullback.snd (SmoothSite.product (SmoothSite.base (Spec (.of k)))
        (SmoothSite.torusPower (.of k) n)).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.fst (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L) n).hom := by
  have h := MorphismProperty.Over.w (pointAmbientIso (n := n) (k := k) (L := L)).inv
  change (pointAmbientIso (k := k) (L := L)).inv.left ≫
    pullback.snd (SmoothSite.product (SmoothSite.base (Spec (.of k)))
        (SmoothSite.torusPower (.of k) n)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
    pullback.fst (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L) n).hom ≫ 𝟙
    _ at h
  simpa only [Category.comp_id] using h

/-- The old base projection is the literal coefficient-field map. -/
@[reassoc (attr := simp)]
theorem pointAmbientProjection_fst :
    pointAmbientProjection (k := k) (L := L) ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) n).hom =
    pullback.fst (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L) n).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  have h := pullback.condition
    (f := (SmoothSite.product (SmoothSite.base (Spec (.of k)))
        (SmoothSite.torusPower (.of k) n)).hom)
    (g := Spec.map (CommRingCat.ofHom (algebraMap k L)))
  change _ ≫ (pullback.fst (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k)
    n).hom ≫
    𝟙 _) = _ at h
  rw [Category.comp_id] at h
  rw [pointAmbientProjection, Category.assoc, h, ← Category.assoc,
    pointAmbientIso_inv_base]

/-- The old torus coordinates are the literal Laurent coefficient projections. -/
@[reassoc (attr := simp)]
theorem pointAmbientProjection_snd :
    pointAmbientProjection (k := k) (L := L) ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) n).hom =
    pullback.snd (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L) n).hom ≫
      torusMap (k := k) (E := L) n := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have h := congrArg (fun f => f.left)
    (SmoothSite.baseChangeProductIso_inv_snd φ (SmoothSite.base (Spec (.of k)))
    (SmoothSite.torusPower (.of k) n))
  have h' := congrArg (fun f => f.left)
    (SmoothSite.productMap_snd
      (SmoothSite.baseChangeBaseIso φ).inv
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) n).inv)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
    SmoothSite.homMk_left] at h h'
  dsimp only [pointAmbientProjection, pointAmbientIso, Iso.trans_inv,
    MorphismProperty.Comma.comp_left, SmoothSite.productIso_inv, torusMap]
  have hn := SmoothSite.baseChange_map_fst φ
    (SmoothSite.productSnd (SmoothSite.base (Spec (.of k))) (SmoothSite.torusPower (.of k) n))
  dsimp only [SmoothSite.productSnd, SmoothSite.homMk_left] at hn
  simp only [Category.assoc]
  have hh := congrArg (fun f => f ≫ pullback.fst (SmoothSite.torusPower (.of k) n).hom φ) h
  rw [Category.assoc] at hh
  rw [← hn, hh]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.fst (SmoothSite.torusPower (.of k) n).hom φ) h').trans
      (Category.assoc _ _ _))

/-- Ambient graph transport cancels the actual factor-comparison isomorphism. -/
theorem graphTransport_pointAmbientProjection :
    (Cor.graphTransportIso L
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) n)).hom ≫
        pointAmbientProjection (k := k) =
    (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (SmoothSite.base (Spec (.of k))) (SmoothSite.torusPower (.of k) n)).inv.left ≫
        pullback.fst (SmoothSite.product (SmoothSite.base (Spec (.of k)))
        (SmoothSite.torusPower (.of k) n)).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  let t := SmoothSite.productIso
    (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) n)
  have ht : t.hom.left ≫ t.inv.left = 𝟙 _ := congrArg (fun h => h.left) t.hom_inv_id
  change t.hom.left ≫ (t.inv.left ≫ _) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ht, Category.id_comp]

/-- Joint comparison with the old ambient point and the new base is faithful. -/
theorem pointAmbient_fieldChange_hom_ext {W : Scheme.{u}}
    {a b : W ⟶ pointAmbient L n}
    (ho : a ≫ pointAmbientProjection (k := k) = b ≫ pointAmbientProjection (k := k))
    (hn : a ≫ pullback.fst (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L)
    n).hom =
      b ≫ pullback.fst (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L)
    n).hom) : a = b := by
  apply (cancel_mono (pointAmbientIso (k := k) (L := L)).inv.left).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pointAmbientProjection] using ho
  · simpa only [Category.assoc, pointAmbientIso_inv_base] using hn

end Ambient

section WholePoint

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Module.Finite k E] [Algebra k L]

local instance baseChange_base_integral (F : Type u) [Field F] :
    IsIntegral (SmoothSite.base (Spec (.of F))).left :=
  inferInstanceAs (IsIntegral (Spec (.of F)))

variable (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (.of E) n)

local instance finitePoint_projection_finite :
    IsFinite (finitePointMap (k := k) n f ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) n).hom) := by
  rw [finitePointMap_fst]
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The entire changed source of the original finite point. -/
abbrev changedPointSupport : Scheme.{u} :=
  FinitePointCorrespondenceBaseChange.support (algebraMap k L) (finitePointMap (k := k) n f)

/-- The actual changed finite point, transported only by the canonical ambient comparisons. -/
def changedPointMap : changedPointSupport (k := k) (L := L) f ⟶ pointAmbient L n :=
  FinitePointCorrespondenceBaseChange.supportMap (algebraMap k L) (finitePointMap (k := k) n f) ≫
    (Cor.graphTransportIso L
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) n)).hom

instance changedPointMap_isFinite : IsFinite (changedPointMap (k := k) (L := L) f) := by
  unfold changedPointMap
  infer_instance

/-- This is the entire original field tensor fiber, not an individual image branch. -/
def changedPointSupportIso : changedPointSupport (k := k) (L := L) f ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  pullback.congrHom
    ((FinitePointCorrespondenceBaseChange.support_structure (finitePointMap (k := k) n f)).trans
      (finitePointMap_fst n f)) rfl

/-- The changed point keeps the original map when projected to the old ambient scheme. -/
@[reassoc (attr := simp)]
theorem changedPointMap_original :
    changedPointMap (k := k) (L := L) f ≫ pointAmbientProjection (k := k) =
      (changedPointSupportIso (k := k) (L := L) f).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ finitePointMap (k := k) n f := by
  rw [changedPointMap, Category.assoc, graphTransport_pointAmbientProjection]
  erw [FinitePointCorrespondenceBaseChange.supportMap_original
    (algebraMap k L) (finitePointMap (k := k) n f)]
  simp [changedPointSupportIso, pullback.congrHom_hom]

/-- The changed point also retains the actual new scalar projection. -/
@[reassoc (attr := simp)]
theorem changedPointMap_base :
    changedPointMap (k := k) (L := L) f ≫
      pullback.fst (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L) n).hom =
    (changedPointSupportIso (k := k) (L := L) f).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  rw [changedPointMap, Category.assoc, Cor.graphTransportIso_hom_fst]
  erw [FinitePointCorrespondenceBaseChange.supportMap_base
    (algebraMap k L) (finitePointMap (k := k) n f)]
  simp [changedPointSupportIso, pullback.congrHom_hom]

/-- The full changed point is the actual cycle field change of the original transfer. -/
theorem toIntegralCycle_baseChange_pointPushforward_graph :
    FiniteCorrespondence.toIntegralCycle
      (baseTorusCycleFieldChange (algebraMap k L) n
        (pointPushforward (k := k) n ((Cor.graphFunctor E).map f))) =
      IntegralCycle.finitePushforward (changedPointMap (k := k) (L := L) f)
        (fundamentalCycle (changedPointSupport (k := k) (L := L) f)) := by
  change FiniteCorrespondence.toIntegralCycle
    (f := (SmoothSite.base (Spec (.of L))).hom) (g := (SmoothSite.torusPower (.of L) n).hom)
    ((Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L)))).inv ≫
      (Cor.fieldBaseChange (algebraMap k L)).map
        (pointPushforward (k := k) n ((Cor.graphFunctor E).map f)) ≫
      (Cor.graphFunctor L).map
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) n).hom) = _
  rw [Cor.toIntegralCycle_graphIso_transport, Cor.fieldBaseChange_map]
  erw [FinitePointCorrespondenceBaseChange.toIntegralCycle_fieldBaseChange_of_finitePoint
      (algebraMap k L) (finitePointMap (k := k) n f) _
      (toIntegralCycle_pointPushforward_graph n f)]
  unfold changedPointMap
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  rfl

end WholePoint

end Motivic.DiagonalCorestrictionBaseChange
