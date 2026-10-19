/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionBaseChange
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual weight-two transfer base change

The finite sum is indexed by the original polynomial places above the source.
Its terms are the existing graph transfers and original raw H22 symbols, using
both literal residue-field images. Signed inputs and both original scalar
projections are retained, without assuming a transfer comparison as input.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Motivic
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers WeightTwoCorestriction
open MilnorK.K3.PolynomialResidue
open scoped BigOperators

universe u

namespace MotivicTest.WeightTwoCorestrictionBaseChange
open _root_.AlgebraicGeometry.Scheme.PolynomialQuotient
open _root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches

variable {k L : Type u} [Field k] [Field L]

local instance polynomialFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

section Projections

variable [Algebra k L] (p : MonicIrreducible k) (a b : (AdjoinRoot p.val)ˣ)

/-- The whole changed quotient still projects to the original scalar point. -/
theorem original_point_projection :
    polynomialChangedPoint (L := L) p a b ≫ pointAmbientProjection (k := k) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.scalarMap (algebraMap k L) p.val)) ≫
        scalarPoint (k := k) (WeightTwoSymbols.rationalPair _ a b) :=
  polynomialChangedPoint_original p a b

/-- The new scalar projection is the original mapped quotient structure map. -/
theorem original_new_scalar_projection :
    polynomialChangedPoint (L := L) p a b ≫
      pullback.fst (SmoothSite.base (Spec (.of L))).hom (target L 2).hom =
        Spec.map (CommRingCat.ofHom (AdjoinRoot.of (p.val.map (algebraMap k L)))) :=
  polynomialChangedPoint_base p a b

/-- Each literal branch retains both residue-field coordinate images. -/
theorem original_branch_coordinates
    (q : AdjoinRoot.IrreducibleBranch (p.val.map (algebraMap k L))) :
    ScalarBranches.branchMap (p.val.map (algebraMap k L)) q ≫
      polynomialChangedPoint (L := L) p a b =
      scalarPoint (k := L) (WeightTwoSymbols.rationalPair (AdjoinRoot q.val.val)
        (Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
          p.val q.val.val q.property).toMonoidHom a)
        (Units.map (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L)
          p.val q.val.val q.property).toMonoidHom b)) :=
  polynomialChangedPoint_branch p a b q

end Projections

section ActualTransfers

variable [CharZero k]

open scoped Classical in
/-- Actual finite correspondences satisfy the whole original places-above formula. -/
theorem actual_cycle_base_change (φ : k →+* L) (p : MonicIrreducible k)
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
              ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom b))) :=
  pointPushforward_graph_baseChange φ p a b

open scoped Classical in
/-- The original raw H22 class obeys the same finite branch-transfer formula. -/
theorem actual_raw_homology_base_change (φ : k →+* L) (p : MonicIrreducible k)
    (a b : (AdjoinRoot p.val)ˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
      (corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p.val) a b)) =
      ∑ q ∈ (placesAbove φ p).attach,
        corestriction (k := L) (WeightTwoSymbols.graphSymbol (AdjoinRoot q.val.val)
          (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom a)
          (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom b)) :=
  corestriction_graphSymbol_baseChange φ p a b

open scoped Classical in
/-- Negative and positive cycle multiplicities pass to every original branch. -/
theorem actual_signed_cycle_base_change (φ : k →+* L) (p : MonicIrreducible k)
    (n : ℤ) (a b : (AdjoinRoot p.val)ˣ) :
    baseTorusCycleFieldChange φ 2
      (pointPushforward (k := k) (n • (Cor.graphFunctor (AdjoinRoot p.val)).map
        (WeightTwoSymbols.rationalPair _ a b))) =
      ∑ q ∈ (placesAbove φ p).attach,
        n • pointPushforward (k := L) ((Cor.graphFunctor (AdjoinRoot q.val.val)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot q.val.val)
            (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
              ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom a)
            (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
              ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom b))) := by
  classical
  erw [map_zsmul, map_zsmul, pointPushforward_graph_baseChange, Finset.smul_sum]

open scoped Classical in
/-- Signed symbols are tested in the original raw homology group itself. -/
theorem actual_signed_raw_base_change (φ : k →+* L) (p : MonicIrreducible k)
    (n : ℤ) (a b : (AdjoinRoot p.val)ˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
      (corestriction (k := k) (n • WeightTwoSymbols.graphSymbol (AdjoinRoot p.val) a b)) =
      ∑ q ∈ (placesAbove φ p).attach,
        n • corestriction (k := L) (WeightTwoSymbols.graphSymbol (AdjoinRoot q.val.val)
          (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom a)
          (Units.map (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom b)) := by
  classical
  rw [map_zsmul, map_zsmul, corestriction_graphSymbol_baseChange, Finset.smul_sum]

end ActualTransfers

open Lean in
run_cmd do
  for name in #[``pointAmbientIso, ``pointAmbientProjection, ``pointAmbientIso_inv_base,
      ``pointAmbientProjection_fst, ``pointAmbientProjection_snd,
      ``graphTransport_pointAmbientProjection, ``pointAmbient_fieldChange_hom_ext,
      ``changedPointSupportIso, ``changedPointMap, ``changedPointMap_original,
      ``changedPointMap_base, ``toIntegralCycle_baseChange_pointPushforward_graph,
      ``polynomialPointSupportIso, ``polynomialChangedPoint,
      ``polynomialChangedPoint_original, ``polynomialChangedPoint_base,
      ``toIntegralCycle_baseChange_polynomialPoint, ``polynomialChangedPoint_branch,
      ``WeightTwoScalarPairChange.unitMap_torusMap,
      ``WeightTwoScalarPairChange.pairMap_torusMap,
      ``WeightTwoScalarPairChange.scalarPoint_rationalPair_comp,
      ``WeightTwoScalarPairChange.rationalPair_scalarSquare,
      ``_root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches.scalarSchemeIso,
      ``scalarSchemeIso_hom_fst,
      ``scalarSchemeIso_hom_snd,
      ``_root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches.scalar_isPullback,
      ``finitePushforward_branchMap,
      ``fundamentalCycle_eq_sum_branches,
      ``scalar_fundamentalCycle_eq_sum_branches,
      ``_root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches.branchMap_scalarMap,
      ``pointPushforward_graph_baseChange, ``corestriction_graphSymbol_baseChange,
      ``original_point_projection, ``original_new_scalar_projection,
      ``original_branch_coordinates, ``actual_cycle_base_change,
      ``actual_raw_homology_base_change, ``actual_signed_cycle_base_change,
      ``actual_signed_raw_base_change] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-two transfer base change uses only standard foundations."

end MotivicTest.WeightTwoCorestrictionBaseChange
