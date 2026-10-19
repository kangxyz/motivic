/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.CorestrictionDegree
public import Motivic.Cohomology.Diagonal.PolynomialPointBaseChange
public import Lean.Util.CollectAxioms

/-! Original all-weight scalar diagrams retain full branch cycles and degree. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open AlgebraicGeometry
open Motivic
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open DiagonalCorestriction DiagonalCorestrictionBaseChange DiagonalCycleSymbols
universe u
namespace MotivicTest.DiagonalCorestrictionScalarDiagrams
open _root_.AlgebraicGeometry.Scheme (IntegralCycle)
variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Degree multiplication acts on the original raw class, not on a replacement group. -/
theorem actual_transfer_restriction [Module.Finite k L] (n : ℕ)
    (x : (motivicRawBaseComplex k n).homology n) :
    corestriction (k := k) (E := L) n
      (HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) n) n x) =
        (Module.finrank k L : ℤ) • x := corestriction_fieldChange n x

local instance polynomialFinite (F : Type u) [Field F]
    (p : MilnorK.PolynomialResidue.MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

/-- The whole finite point's scalar cycle is its literal changed source fundamental cycle. -/
theorem actual_whole_polynomial_cycle (n : ℕ)
    (p : MilnorK.PolynomialResidue.MonicIrreducible k)
    (a : Fin n → (AdjoinRoot p.val)ˣ) :
    FiniteCorrespondence.toIntegralCycle
      (baseTorusCycleFieldChange (algebraMap k L) n
        (pointPushforward (k := k) n ((Cor.graphFunctor (AdjoinRoot p.val)).map
          (rationalTuple _ n a)))) =
      IntegralCycle.finitePushforward (polynomialChangedPoint (L := L) p a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (Spec (.of (AdjoinRoot (p.val.map
            (algebraMap k L)))))) :=
  toIntegralCycle_baseChange_polynomialPoint p a

open Lean in
run_cmd do
  for name in #[``actual_transfer_restriction, ``actual_whole_polynomial_cycle,
      ``pointPushforward_graph_baseChange_algebraMap,
      ``polynomialChangedPoint_branch,
      ``Motivic.DiagonalScalarTupleChange.rationalTuple_scalarSquare] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original all-weight transfer scalar diagrams: standard foundations only."

end MotivicTest.DiagonalCorestrictionScalarDiagrams
