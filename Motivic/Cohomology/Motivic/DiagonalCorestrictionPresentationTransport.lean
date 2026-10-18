/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalScalarTupleChange
public import Motivic.Cohomology.Motivic.DiagonalFieldChange

/-!
# Presentation transport for actual all-weight diagonal transfers

An actual algebra equivalence between two original finite extension fields
identifies the finite-point maps before passing to cycles. The fundamental
cycle is invariant under the resulting spectrum isomorphism, so the genuine
corestrictions of the all-weight Milnor symbols agree. No compatibility with
an independently defined norm is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Motivic.DiagonalCorestriction

open DiagonalCycleSymbols DiagonalMilnorSymbol
open WeightTwoCorestriction WeightTwoCubicBoundary

variable {k E F : Type u} [Field k] [Field E] [Field F]
  [Algebra k E] [Algebra k F]

/-- An actual algebra map retains the original base structure and every tuple coordinate. -/
theorem rationalTuple_algHom (φ : E →ₐ[k] F) (n : ℕ) (a : Fin n → Eˣ) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (rationalTuple E n a).left ≫ torusMap (k := k) (E := E) n =
    (rationalTuple F n (fun i => Units.map φ.toRingHom.toMonoidHom (a i))).left ≫
      torusMap (k := k) (E := F) n := by
  have hφ : φ.toRingHom.comp (algebraMap k E) = algebraMap k F := by
    ext r
    exact φ.commutes r
  apply torusPower_scheme_hom_ext n
  · have he := MorphismProperty.Over.w (rationalTuple E n a)
    have hf := MorphismProperty.Over.w
      (rationalTuple F n (fun i => Units.map φ.toRingHom.toMonoidHom (a i)))
    change (rationalTuple E n a).left ≫ (SmoothSite.torusPower (.of E) n).hom =
      𝟙 _ at he
    change (rationalTuple F n (fun i => Units.map φ.toRingHom.toMonoidHom (a i))).left ≫
      (SmoothSite.torusPower (.of F) n).hom = 𝟙 _ at hf
    simp only [Category.assoc, torusMap_projection]
    rw [← Category.assoc (rationalTuple E n a).left, he, Category.id_comp]
    rw [← Category.assoc
      (rationalTuple F n (fun i => Units.map φ.toRingHom.toMonoidHom (a i))).left,
      hf, Category.id_comp, ← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom hφ)
  · intro i
    simp only [Category.assoc, torusMap_coordinate]
    have he := congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of E) n
        (fun j => WeightOnePointNorm.rationalTorusPoint E (a j)) i)
    have hf := congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of F) n
        (fun j => WeightOnePointNorm.rationalTorusPoint F
          (Units.map φ.toRingHom.toMonoidHom (a j))) i)
    dsimp only [MorphismProperty.Comma.comp_left] at he hf
    change (rationalTuple E n a).left ≫
      (SmoothSite.torusCoordinate (.of E) n i).left = _ at he
    change (rationalTuple F n (fun i => Units.map φ.toRingHom.toMonoidHom (a i))).left ≫
      (SmoothSite.torusCoordinate (.of F) n i).left = _ at hf
    rw [← Category.assoc (rationalTuple E n a).left, he,
      ← Category.assoc
        (rationalTuple F n (fun i => Units.map φ.toRingHom.toMonoidHom (a i))).left, hf]
    rw [rationalTorusPoint_scalar, rationalTorusPoint_scalar]
    exact unitMap_comp (algebraMap k E) (algebraMap k F) φ.toRingHom
      (a i) (Units.map φ.toRingHom.toMonoidHom (a i)) hφ rfl

/-- Presentation transport is an equality of the actual original finite-point maps. -/
theorem finitePointMap_algHom (φ : E →ₐ[k] F) (n : ℕ) (a : Fin n → Eˣ) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      finitePointMap (k := k) n (rationalTuple E n a) =
    finitePointMap (k := k) n
      (rationalTuple F n (fun i => Units.map φ.toRingHom.toMonoidHom (a i))) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finitePointMap_fst]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact φ.commutes r
  · simp only [Category.assoc, finitePointMap_snd]
    exact rationalTuple_algHom φ n a

variable [Module.Finite k E] [Module.Finite k F]

/-- An algebra equivalence preserves the entire transferred graph, including image degrees. -/
theorem pointPushforward_graph_algEquiv (ε : E ≃ₐ[k] F) (n : ℕ) (a : Fin n → Eˣ) :
    pointPushforward (k := k) n ((Cor.graphFunctor E).map (rationalTuple E n a)) =
    pointPushforward (k := k) n ((Cor.graphFunctor F).map
      (rationalTuple F n (fun i => Units.map ε.toRingHom.toMonoidHom (a i)))) := by
  let e := Scheme.Spec.mapIso ε.toRingEquiv.toCommRingCatIso.op
  have he : e.hom = Spec.map (CommRingCat.ofHom ε.toRingHom) := rfl
  have : IsIso (Spec.map (CommRingCat.ofHom ε.toRingHom)) := by
    rw [← he]
    infer_instance
  have hε : Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
      finitePointMap (k := k) n (rationalTuple E n a) =
      finitePointMap (k := k) n
        (rationalTuple F n (fun i => Units.map ε.toRingHom.toMonoidHom (a i))) :=
    finitePointMap_algHom ε.toAlgHom n a
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_pointPushforward_graph, toIntegralCycle_pointPushforward_graph,
    ← finitePushforward_fundamentalCycle (Spec.map (CommRingCat.ofHom ε.toRingHom)),
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr hε]

/-- The genuine raw graph transfers are independent of the chosen algebra presentation. -/
theorem corestriction_graphSymbol_algEquiv (ε : E ≃ₐ[k] F) (n : ℕ)
    (a : Fin n → Eˣ) :
    corestriction (k := k) n (graphSymbol E n a) =
    corestriction (k := k) n
      (graphSymbol F n (fun i => Units.map ε.toRingHom.toMonoidHom (a i))) := by
  rw [corestriction_graphSymbol, corestriction_graphSymbol, pointPushforward_graph_algEquiv ε]

variable [CharZero E] [CharZero F]

/-- Actual diagonal transfer of every Milnor class survives an algebra presentation change. -/
theorem corestriction_rawSymbol_algEquiv (ε : E ≃ₐ[k] F) (n : ℕ)
    (x : MilnorK.K E n) :
    corestriction (k := k) (E := E) n (rawSymbol E n x) =
    corestriction (k := k) (E := F) n (rawSymbol F n (MilnorK.map n ε.toRingHom x)) := by
  have h : (corestriction (k := k) (E := E) n).comp (rawSymbol E n) =
      (corestriction (k := k) (E := F) n).comp
        ((rawSymbol F n).comp (MilnorK.map n ε.toRingHom).toAddMonoidHom) := by
    apply MilnorK.addHom_ext
    intro a
    change corestriction (k := k) n (rawSymbol E n (MilnorK.symbol a)) =
      corestriction (k := k) n
        (rawSymbol F n (MilnorK.map n ε.toRingHom (MilnorK.symbol a)))
    rw [rawSymbol_symbol, MilnorK.map_symbol, rawSymbol_symbol]
    exact corestriction_graphSymbol_algEquiv ε n a
  exact DFunLike.congr_fun h x

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of F))) AddCommGrpCat.{u + 1})]

/-- The same presentation law holds on the original derived diagonal motivic groups. -/
theorem motivicCorestriction_motivicSymbol_algEquiv (ε : E ≃ₐ[k] F) (n : ℕ)
    (x : MilnorK.K E n) :
    motivicCorestriction (k := k) (E := E) n (motivicSymbol E n x) =
    motivicCorestriction (k := k) (E := F) n
      (motivicSymbol F n (MilnorK.map n ε.toRingHom x)) := by
  apply (motivicRawBaseEvaluationComparison k n n).injective
  rw [motivicCorestriction_comparison, motivicCorestriction_comparison,
    motivicSymbol_comparison, motivicSymbol_comparison, corestriction_rawSymbol_algEquiv ε]

end Motivic.DiagonalCorestriction
