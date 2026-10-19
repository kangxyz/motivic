/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.BoundaryNorm
public import Motivic.Cohomology.Diagonal.ReducedPointNorm

/-! # Actual reduced singular cofaces evaluated in every Milnor degree -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.DiagonalBoundaryEvaluation
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers WeightOneBoundaryNorm
variable (k : Type u) [Field k] [CharZero k] (q : ℕ)

/-- The point norm on the actual degree-zero singular quotient,
via the proved base identification. -/
def degreeZeroNorm : sections (reducedTorus k q)
    (Cor.simplexProduct (WeightOnePointNorm.point k) 0) →+ MilnorK.K k q :=
  (DiagonalReducedPointNorm.reducedNorm k q).comp
    (transfer (reducedTorus k q) (zeroProductIso k).inv).hom

/-- Its formula on every actual signed represented zero-simplex cycle. -/
theorem degreeZeroNorm_quotient
    (α : Cor.simplexProduct (WeightOnePointNorm.point k) 0 ⟶ DiagonalCycleSymbols.target k q) :
    degreeZeroNorm k q ((toReducedTorus k q).hom.app
      (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0)) (ULift.up α)) =
        DiagonalPointNorm.cycleValue k q ((zeroProductIso k).inv ≫ α) := by
  change DiagonalReducedPointNorm.reducedNorm k q
    (transfer (reducedTorus k q) (zeroProductIso k).inv _) = _
  rw [reducedTorus_transfer_apply, DiagonalReducedPointNorm.reducedNorm_quotient]

/-- Each actual reduced product coface has exactly its endpoint norm, with no hidden sign. -/
theorem degreeZeroNorm_face_quotient (i : Fin 2)
    (α : Cor.simplexProduct (WeightOnePointNorm.point k) 1 ⟶ DiagonalCycleSymbols.target k q) :
    degreeZeroNorm k q
      (transfer (reducedTorus k q)
        ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i)
        ((toReducedTorus k q).hom.app
          (op (Cor.simplexProduct (WeightOnePointNorm.point k) 1)) (ULift.up α))) =
      DiagonalPointNorm.cycleValue k q
        ((Cor.graphFunctor k).map (facePoint k i) ≫ (simplexProductIso k 1).inv ≫ α) := by
  have h := reducedTorus_transfer_apply k q
    (show Cor.simplexProduct (WeightOnePointNorm.point k) 0 ⟶
        Cor.simplexProduct (WeightOnePointNorm.point k) 1 from
      (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i) α
  calc
    _ = degreeZeroNorm k q ((toReducedTorus k q).hom.app
        (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0))
        (ULift.up ((Cor.simplexProductCosimplicial
          (WeightOnePointNorm.point k)).δ i ≫ α))) := congrArg (degreeZeroNorm k q) h
    _ = _ := by
      rw [degreeZeroNorm_quotient, ← Category.assoc, zeroProductIso_inv_face, Category.assoc]


end Motivic.DiagonalBoundaryEvaluation
