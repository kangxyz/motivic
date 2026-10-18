/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionMixed
public import Motivic.Cohomology.Motivic.WeightTwoPolynomialTransfer
public import Motivic.AlgebraicGeometry.Correspondences.FinitePointBaseChange
public import Motivic.Cohomology.Motivic.WeightTwoScalarPairChange
public import Motivic.Aglib.AlgebraicGeometry.AdjoinRootScalarBranches
public import Aglib.KTheory.MilnorK.K3.ResidueBaseChangeSupport

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

namespace Motivic.WeightTwoCorestriction

open PresheafWithTransfers WeightOnePointNorm WeightOneBoundaryNorm

/-- The original base-point and two-torus ambient scheme. -/
abbrev pointAmbient (F : Type u) [Field F] : Scheme.{u} :=
  (SmoothSite.product (SmoothSite.base (Spec (.of F))) (target F 2)).left

section Ambient

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The literal whole ambient scalar-extension comparison. -/
def pointAmbientIso :
    (SmoothSite.fieldBaseChange (algebraMap k L)).obj
      (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)) ≅
    SmoothSite.product (SmoothSite.base (Spec (.of L))) (target L 2) :=
  SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (SmoothSite.base (Spec (.of k))) (target k 2) ≪≫
    SmoothSite.productIso
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) 2)

/-- The old ambient projection, retaining the original coefficient map. -/
def pointAmbientProjection : pointAmbient L ⟶ pointAmbient k :=
  (pointAmbientIso (k := k) (L := L)).inv.left ≫
    pullback.fst (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- The new base projection is exactly the other projection of the whole pullback. -/
@[reassoc (attr := simp)]
theorem pointAmbientIso_inv_base :
    (pointAmbientIso (k := k) (L := L)).inv.left ≫
      pullback.snd (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom := by
  have h := MorphismProperty.Over.w (pointAmbientIso (k := k) (L := L)).inv
  change (pointAmbientIso (k := k) (L := L)).inv.left ≫
    pullback.snd (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
    pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

/-- The old base projection is the literal coefficient-field map. -/
@[reassoc (attr := simp)]
theorem pointAmbientProjection_fst :
    pointAmbientProjection (k := k) (L := L) ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom =
    pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  have h := pullback.condition
    (f := (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)).hom)
    (g := Spec.map (CommRingCat.ofHom (algebraMap k L)))
  change _ ≫ (pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom ≫
    𝟙 _) = _ at h
  rw [Category.comp_id] at h
  rw [pointAmbientProjection, Category.assoc, h, ← Category.assoc,
    pointAmbientIso_inv_base]

/-- The old torus coordinates are the literal Laurent coefficient projections. -/
@[reassoc (attr := simp)]
theorem pointAmbientProjection_snd :
    pointAmbientProjection (k := k) (L := L) ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k 2).hom =
    pullback.snd (SmoothSite.base (Spec (.of L))).hom (target L 2).hom ≫
      torusMap (k := k) (E := L) 2 := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have h := congrArg (fun f => f.left)
    (SmoothSite.baseChangeProductIso_inv_snd φ (SmoothSite.base (Spec (.of k))) (target k 2))
  have h' := congrArg (fun f => f.left)
    (SmoothSite.productMap_snd
      (SmoothSite.baseChangeBaseIso φ).inv
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) 2).inv)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
    SmoothSite.homMk_left] at h h'
  dsimp only [pointAmbientProjection, pointAmbientIso, Iso.trans_inv,
    MorphismProperty.Comma.comp_left, SmoothSite.productIso_inv, torusMap]
  have hn := SmoothSite.baseChange_map_fst φ
    (SmoothSite.productSnd (SmoothSite.base (Spec (.of k))) (target k 2))
  dsimp only [SmoothSite.productSnd, SmoothSite.homMk_left] at hn
  simp only [Category.assoc]
  have hh := congrArg (fun f => f ≫ pullback.fst (target k 2).hom φ) h
  rw [Category.assoc] at hh
  rw [← hn, hh]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.fst (target k 2).hom φ) h').trans
      (Category.assoc _ _ _))

/-- Ambient graph transport cancels the actual factor-comparison isomorphism. -/
theorem graphTransport_pointAmbientProjection :
    (Cor.graphTransportIso L
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) 2)).hom ≫
        pointAmbientProjection (k := k) =
    (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (SmoothSite.base (Spec (.of k))) (target k 2)).inv.left ≫
        pullback.fst (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  let t := SmoothSite.productIso
    (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) 2)
  have ht : t.hom.left ≫ t.inv.left = 𝟙 _ := congrArg (fun h => h.left) t.hom_inv_id
  change t.hom.left ≫ (t.inv.left ≫ _) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ht, Category.id_comp]

/-- Joint comparison with the old ambient point and the new base is faithful. -/
theorem pointAmbient_fieldChange_hom_ext {W : Scheme.{u}}
    {a b : W ⟶ pointAmbient L}
    (ho : a ≫ pointAmbientProjection (k := k) = b ≫ pointAmbientProjection (k := k))
    (hn : a ≫ pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom =
      b ≫ pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom) : a = b := by
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

variable (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2)

local instance scalarPoint_projection_finite :
    IsFinite (scalarPoint (k := k) f ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom) := by
  rw [scalarPoint_fst]
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The entire changed source of the original finite point. -/
abbrev changedPointSupport : Scheme.{u} :=
  FinitePointCorrespondenceBaseChange.support (algebraMap k L) (scalarPoint (k := k) f)

/-- The actual changed finite point, transported only by the canonical ambient comparisons. -/
def changedPointMap : changedPointSupport (k := k) (L := L) f ⟶ pointAmbient L :=
  FinitePointCorrespondenceBaseChange.supportMap (algebraMap k L) (scalarPoint (k := k) f) ≫
    (Cor.graphTransportIso L
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) 2)).hom

instance changedPointMap_isFinite : IsFinite (changedPointMap (k := k) (L := L) f) := by
  unfold changedPointMap
  infer_instance

/-- This is the entire original field tensor fiber, not an individual image branch. -/
def changedPointSupportIso : changedPointSupport (k := k) (L := L) f ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  pullback.congrHom
    ((FinitePointCorrespondenceBaseChange.support_structure (scalarPoint (k := k) f)).trans
      (scalarPoint_fst f)) rfl

/-- The changed point keeps the original map when projected to the old ambient scheme. -/
@[reassoc (attr := simp)]
theorem changedPointMap_original :
    changedPointMap (k := k) (L := L) f ≫ pointAmbientProjection (k := k) =
      (changedPointSupportIso (k := k) (L := L) f).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ scalarPoint (k := k) f := by
  rw [changedPointMap, Category.assoc, graphTransport_pointAmbientProjection]
  erw [FinitePointCorrespondenceBaseChange.supportMap_original
    (algebraMap k L) (scalarPoint (k := k) f)]
  simp [changedPointSupportIso, pullback.congrHom_hom]

/-- The changed point also retains the actual new scalar projection. -/
@[reassoc (attr := simp)]
theorem changedPointMap_base :
    changedPointMap (k := k) (L := L) f ≫
      pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom =
    (changedPointSupportIso (k := k) (L := L) f).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  rw [changedPointMap, Category.assoc, Cor.graphTransportIso_hom_fst]
  erw [FinitePointCorrespondenceBaseChange.supportMap_base
    (algebraMap k L) (scalarPoint (k := k) f)]
  simp [changedPointSupportIso, pullback.congrHom_hom]

/-- The full changed point is the actual cycle field change of the original transfer. -/
theorem toIntegralCycle_baseChange_pointPushforward_graph :
    FiniteCorrespondence.toIntegralCycle
      (baseTorusCycleFieldChange (algebraMap k L) 2
        (pointPushforward (k := k) ((Cor.graphFunctor E).map f))) =
      IntegralCycle.finitePushforward (changedPointMap (k := k) (L := L) f)
        (fundamentalCycle (changedPointSupport (k := k) (L := L) f)) := by
  change FiniteCorrespondence.toIntegralCycle
    (f := (SmoothSite.base (Spec (.of L))).hom) (g := (target L 2).hom)
    ((Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L)))).inv ≫
      (Cor.fieldBaseChange (algebraMap k L)).map
        (pointPushforward (k := k) ((Cor.graphFunctor E).map f)) ≫
      (Cor.graphFunctor L).map
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k L)) 2).hom) = _
  rw [Cor.toIntegralCycle_graphIso_transport, Cor.fieldBaseChange_map]
  erw [FinitePointCorrespondenceBaseChange.toIntegralCycle_fieldBaseChange_of_finitePoint
      (algebraMap k L) (scalarPoint (k := k) f) _
      (toIntegralCycle_pointPushforward_graph f)]
  unfold changedPointMap
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  rfl

end WholePoint


section Polynomial

open Polynomial MilnorK.K3.PolynomialResidue AdjoinRootScalarBranches

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

local instance polynomialFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

variable (p : MonicIrreducible k) (a b : (AdjoinRoot p.val)ˣ)

/-- The entire mapped quotient is the original finite point's whole scalar support. -/
def polynomialPointSupportIso :
    Spec (.of (AdjoinRoot (p.val.map (algebraMap k L)))) ≅
      changedPointSupport (k := k) (L := L) (WeightTwoSymbols.rationalPair _ a b) :=
  scalarSchemeIso (algebraMap k L) p.val ≪≫ pullbackSymmetry _ _ ≪≫
    (changedPointSupportIso (k := k) (L := L) (WeightTwoSymbols.rationalPair _ a b)).symm

/-- The full mapped quotient carries the changed pair before decomposition into branches. -/
def polynomialChangedPoint :
    Spec (.of (AdjoinRoot (p.val.map (algebraMap k L)))) ⟶ pointAmbient L :=
  (polynomialPointSupportIso (L := L) p a b).hom ≫
    changedPointMap (k := k) (L := L) (WeightTwoSymbols.rationalPair _ a b)

instance polynomialChangedPoint_isFinite : IsFinite (polynomialChangedPoint (L := L) p a b) := by
  unfold polynomialChangedPoint
  infer_instance

/-- The old projection is the literal coefficient-extension quotient homomorphism. -/
@[reassoc (attr := simp)]
theorem polynomialChangedPoint_original :
    polynomialChangedPoint (L := L) p a b ≫ pointAmbientProjection (k := k) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.scalarMap (algebraMap k L) p.val)) ≫
        scalarPoint (k := k) (WeightTwoSymbols.rationalPair _ a b) := by
  simp only [polynomialChangedPoint, Category.assoc, changedPointMap_original,
    polynomialPointSupportIso, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  erw [pullbackSymmetry_hom_comp_fst_assoc, scalarSchemeIso_hom_snd_assoc]

/-- The new projection is the literal scalar structure of the whole mapped quotient. -/
@[reassoc (attr := simp)]
theorem polynomialChangedPoint_base :
    polynomialChangedPoint (L := L) p a b ≫
      pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom =
        Spec.map (CommRingCat.ofHom (AdjoinRoot.of (p.val.map (algebraMap k L)))) := by
  simp only [polynomialChangedPoint, Category.assoc, changedPointMap_base,
    polynomialPointSupportIso, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  erw [pullbackSymmetry_hom_comp_snd, scalarSchemeIso_hom_fst]

/-- The original transferred graph extends to the whole mapped polynomial quotient cycle. -/
theorem toIntegralCycle_baseChange_polynomialPoint :
    FiniteCorrespondence.toIntegralCycle
      (baseTorusCycleFieldChange (algebraMap k L) 2
        (pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p.val)).map
          (WeightTwoSymbols.rationalPair _ a b)))) =
      IntegralCycle.finitePushforward (polynomialChangedPoint (L := L) p a b)
        (fundamentalCycle (Spec (.of (AdjoinRoot (p.val.map (algebraMap k L)))))) := by
  rw [toIntegralCycle_baseChange_pointPushforward_graph]
  unfold polynomialChangedPoint
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  erw [finitePushforward_fundamentalCycle (polynomialPointSupportIso (L := L) p a b).hom]

/-- Both branch coordinates are the images under the original residue-field map. -/
theorem polynomialChangedPoint_branch
    (q : AdjoinRoot.IrreducibleBranch (p.val.map (algebraMap k L))) :
    branchMap (p.val.map (algebraMap k L)) q ≫ polynomialChangedPoint (L := L) p a b =
      scalarPoint (k := L) (WeightTwoSymbols.rationalPair (AdjoinRoot q.val.val)
        (Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
          p.val q.val.val q.property).toMonoidHom a)
        (Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
          p.val q.val.val q.property).toMonoidHom b)) := by
  let ψ := Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
    p.val q.val.val q.property
  have hψ : ψ.comp (algebraMap k (AdjoinRoot p.val)) =
      (algebraMap L (AdjoinRoot q.val.val)).comp (algebraMap k L) := by
    apply RingHom.ext
    intro x
    exact Polynomial.LocalResidue.adjoinRootMap_algebraMap
      (algebraMap k L) p.val q.val.val q.property x
  apply pointAmbient_fieldChange_hom_ext (k := k)
  · rw [Category.assoc, polynomialChangedPoint_original, ← Category.assoc,
      branchMap_scalarMap]
    apply pullback.hom_ext
    · simp only [Category.assoc, scalarPoint_fst, scalarPoint_fst_assoc, pointAmbientProjection_fst]
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom hψ)
    · simp only [Category.assoc, scalarPoint_snd, scalarPoint_snd_assoc, pointAmbientProjection_snd]
      exact WeightTwoScalarPairChange.rationalPair_scalarSquare ψ hψ a b
  · rw [Category.assoc, polynomialChangedPoint_base, scalarPoint_fst]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1

open scoped Classical in
/-- Squarefreeness in characteristic zero decomposes the whole scalar quotient
into every original polynomial place, each with its actual coefficient one. -/
theorem polynomialFundamentalCycle_eq_sum_placesAbove [CharZero k] :
    fundamentalCycle (Spec (.of (AdjoinRoot (p.val.map (algebraMap k L))))) =
      ∑ q ∈ (placesAbove (algebraMap k L) p).attach,
        IntegralCycle.finitePushforward
          (branchMap (p.val.map (algebraMap k L))
            ⟨q.val, (mem_placesAbove (algebraMap k L) p q.val).mp q.property⟩)
          (fundamentalCycle (Spec (.of (AdjoinRoot q.val.val)))) := by
  classical
  let : Module.Finite L (AdjoinRoot (p.val.map (algebraMap k L))) :=
    (p.property.1.map (algebraMap k L)).finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot (p.val.map (algebraMap k L))) := .of_finite L _
  let : Fintype (MaximalSpectrum (AdjoinRoot (p.val.map (algebraMap k L)))) :=
    Fintype.ofFinite _
  let : Fintype (AdjoinRoot.IrreducibleBranch (p.val.map (algebraMap k L))) :=
    Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot (p.val.map (algebraMap k L))))
      (AdjoinRoot.branchEquivMaximal (p.val.map (algebraMap k L))
        (p.property.1.map (algebraMap k L)).ne_zero).symm
  have h := scalar_fundamentalCycle_eq_sum_branches (algebraMap k L) p.val p.property.1
  dsimp only at h
  rw [h, Finset.attach_eq_univ]
  symm
  apply Fintype.sum_equiv
    (Equiv.subtypeEquivRight (fun q => mem_placesAbove (algebraMap k L) p q))
  intro q
  rfl

open scoped Classical in
/-- Actual finite graph transfer commutes with the given scalar extension after
summing all residue branches. Distinct branches need not have distinct images. -/
theorem pointPushforward_graph_baseChange_algebraMap [CharZero k] :
    baseTorusCycleFieldChange (algebraMap k L) 2
      (pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p.val)).map
        (WeightTwoSymbols.rationalPair _ a b))) =
      ∑ q ∈ (placesAbove (algebraMap k L) p).attach,
        pointPushforward (k := L) ((Cor.graphFunctor (AdjoinRoot q.val.val)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot q.val.val)
            (Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
              p.val q.val.val
              ((mem_placesAbove (algebraMap k L) p q.val).mp q.property)).toMonoidHom a)
            (Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
              p.val q.val.val
              ((mem_placesAbove (algebraMap k L) p q.val).mp q.property)).toMonoidHom b))) := by
  classical
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_baseChange_polynomialPoint,
    polynomialFundamentalCycle_eq_sum_placesAbove]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [toIntegralCycle_pointPushforward_graph,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr (polynomialChangedPoint_branch p a b
      ⟨q.val, (mem_placesAbove (algebraMap k L) p q.val).mp q.property⟩)]

end Polynomial

section Endpoints

open Polynomial MilnorK.K3.PolynomialResidue

variable {k L : Type u} [Field k] [Field L] [CharZero k]

local instance polynomialEndpointFinite (F : Type u) [Field F]
    (p : MonicIrreducible F) : Module.Finite F (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

open scoped Classical in
/-- The actual cycle Mackey formula for an arbitrary coefficient-field homomorphism. -/
theorem pointPushforward_graph_baseChange (φ : k →+* L) (p : MonicIrreducible k)
    (a b : (AdjoinRoot p.val)ˣ) :
    baseTorusCycleFieldChange φ 2
      (pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p.val)).map
        (WeightTwoSymbols.rationalPair _ a b))) =
      ∑ q ∈ (placesAbove φ p).attach,
        pointPushforward (k := L) ((Cor.graphFunctor (AdjoinRoot q.val.val)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot q.val.val)
            (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
              ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom a)
            (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
              ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom b))) := by
  let := φ.toAlgebra
  exact pointPushforward_graph_baseChange_algebraMap p a b

open scoped Classical in
/-- Restriction of the original raw H22 transfer is the sum of the original
raw transfers at every place above the source, with both literal residue images. -/
theorem corestriction_graphSymbol_baseChange (φ : k →+* L) (p : MonicIrreducible k)
    (a b : (AdjoinRoot p.val)ˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
      (corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p.val) a b)) =
      ∑ q ∈ (placesAbove φ p).attach,
        corestriction (k := L) (WeightTwoSymbols.graphSymbol (AdjoinRoot q.val.val)
          (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom a)
          (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom b)) := by
  classical
  simp only [WeightTwoSymbols.graphSymbol, corestriction_cycleClass,
    WeightTwoFieldChange.cycleClass_fieldChange, pointPushforward_graph_baseChange, map_sum]

end Endpoints

end Motivic.WeightTwoCorestriction
