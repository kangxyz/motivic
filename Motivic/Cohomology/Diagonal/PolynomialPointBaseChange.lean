/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.CorestrictionBaseChange
public import Motivic.Cohomology.Diagonal.ScalarTupleChange
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.ScalarBranches
public import Aglib.KTheory.MilnorK.Residue.BaseChangeSupport

/-! # Every original scalar branch of an arbitrary-weight transferred polynomial point -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
universe u
namespace Motivic.DiagonalCorestrictionBaseChange
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open DiagonalCorestriction
open DiagonalCycleSymbols
variable {n : ℕ}

section Polynomial

open Polynomial
open MilnorK.PolynomialResidue
open _root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

local instance polynomialFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

variable (p : MonicIrreducible k) (a : Fin n → (AdjoinRoot p.val)ˣ)

/-- The entire mapped quotient is the original finite point's whole scalar support. -/
def polynomialPointSupportIso :
    Spec (.of (AdjoinRoot (p.val.map (algebraMap k L)))) ≅
      changedPointSupport (k := k) (L := L) (DiagonalCycleSymbols.rationalTuple _ n a) :=
  scalarSchemeIso (algebraMap k L) p.val ≪≫ pullbackSymmetry _ _ ≪≫
    (changedPointSupportIso (k := k) (L := L) (DiagonalCycleSymbols.rationalTuple _ n a)).symm

/-- The full mapped quotient carries the changed pair before decomposition into branches. -/
def polynomialChangedPoint :
    Spec (.of (AdjoinRoot (p.val.map (algebraMap k L)))) ⟶ pointAmbient L n :=
  (polynomialPointSupportIso (L := L) p a).hom ≫
    changedPointMap (k := k) (L := L) (DiagonalCycleSymbols.rationalTuple _ n a)

instance polynomialChangedPoint_isFinite : IsFinite (polynomialChangedPoint (L := L) p a) := by
  unfold polynomialChangedPoint
  infer_instance

/-- The old projection is the literal coefficient-extension quotient homomorphism. -/
@[reassoc (attr := simp)]
theorem polynomialChangedPoint_original :
    polynomialChangedPoint (L := L) p a ≫ pointAmbientProjection (k := k) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.scalarMap (algebraMap k L) p.val)) ≫
        finitePointMap (k := k) n (DiagonalCycleSymbols.rationalTuple _ n a) := by
  simp only [polynomialChangedPoint, Category.assoc, changedPointMap_original,
    polynomialPointSupportIso, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  erw [pullbackSymmetry_hom_comp_fst_assoc, scalarSchemeIso_hom_snd_assoc]

/-- The new projection is the literal scalar structure of the whole mapped quotient. -/
@[reassoc (attr := simp)]
theorem polynomialChangedPoint_base :
    polynomialChangedPoint (L := L) p a ≫
      pullback.fst (SmoothSite.base (Spec (.of L))).hom (SmoothSite.torusPower (.of L) n).hom =
        Spec.map (CommRingCat.ofHom (AdjoinRoot.of (p.val.map (algebraMap k L)))) := by
  simp only [polynomialChangedPoint, Category.assoc, changedPointMap_base,
    polynomialPointSupportIso, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  erw [pullbackSymmetry_hom_comp_snd, scalarSchemeIso_hom_fst]

/-- The original transferred graph extends to the whole mapped polynomial quotient cycle. -/
theorem toIntegralCycle_baseChange_polynomialPoint :
    FiniteCorrespondence.toIntegralCycle
      (baseTorusCycleFieldChange (algebraMap k L) n
        (pointPushforward (k := k) n ((Cor.graphFunctor (AdjoinRoot p.val)).map
          (DiagonalCycleSymbols.rationalTuple _ n a)))) =
      IntegralCycle.finitePushforward (polynomialChangedPoint (L := L) p a)
        (fundamentalCycle (Spec (.of (AdjoinRoot (p.val.map (algebraMap k L)))))) := by
  rw [toIntegralCycle_baseChange_pointPushforward_graph]
  unfold polynomialChangedPoint
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  erw [finitePushforward_fundamentalCycle (polynomialPointSupportIso (L := L) p a).hom]

/-- Every original branch carries the full tuple under its literal quotient-field map. -/
theorem polynomialChangedPoint_branch
    (q : AdjoinRoot.IrreducibleBranch (p.val.map (algebraMap k L))) :
    branchMap (p.val.map (algebraMap k L)) q ≫ polynomialChangedPoint (L := L) p a =
      finitePointMap (k := L) n (rationalTuple (AdjoinRoot q.val.val) n
        (fun i => Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
          p.val q.val.val q.property).toMonoidHom (a i))) := by
  let ψ := Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
    p.val q.val.val q.property
  have hψ : ψ.comp (algebraMap k (AdjoinRoot p.val)) =
      (algebraMap L (AdjoinRoot q.val.val)).comp (algebraMap k L) := by
    ext x
    exact Polynomial.LocalResidue.adjoinRootMap_algebraMap
      (algebraMap k L) p.val q.val.val q.property x
  apply pointAmbient_fieldChange_hom_ext (k := k)
  · rw [Category.assoc, polynomialChangedPoint_original, ← Category.assoc,
      branchMap_scalarMap]
    apply pullback.hom_ext
    · simp only [Category.assoc, finitePointMap_fst, finitePointMap_fst_assoc,
        pointAmbientProjection_fst]
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom hψ)
    · simp only [Category.assoc, finitePointMap_snd, finitePointMap_snd_assoc,
        pointAmbientProjection_snd]
      exact DiagonalScalarTupleChange.rationalTuple_scalarSquare ψ hψ n a
  · rw [Category.assoc, polynomialChangedPoint_base, finitePointMap_fst]
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
/-- The full actual graph-transfer Mackey formula, retaining every original branch. -/
theorem pointPushforward_graph_baseChange_algebraMap [CharZero k] :
    baseTorusCycleFieldChange (algebraMap k L) n
      (pointPushforward (k := k) n ((Cor.graphFunctor (AdjoinRoot p.val)).map
        (rationalTuple _ n a))) =
      ∑ q ∈ (placesAbove (algebraMap k L) p).attach,
        pointPushforward (k := L) n ((Cor.graphFunctor (AdjoinRoot q.val.val)).map
          (rationalTuple (AdjoinRoot q.val.val) n
            (fun i => Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
              p.val q.val.val
              ((mem_placesAbove (algebraMap k L) p q.val).mp q.property)).toMonoidHom (a i)))) := by
  classical
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_baseChange_polynomialPoint,
    polynomialFundamentalCycle_eq_sum_placesAbove]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [toIntegralCycle_pointPushforward_graph,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr (polynomialChangedPoint_branch p a
      ⟨q.val, (mem_placesAbove (algebraMap k L) p q.val).mp q.property⟩)]

end Polynomial
end Motivic.DiagonalCorestrictionBaseChange
