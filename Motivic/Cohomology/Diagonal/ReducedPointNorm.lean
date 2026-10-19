/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.FinitePointEvaluation

/-! # The actual all-weight finite-point evaluator on the reduced torus quotient -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.DiagonalReducedPointNorm
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers
open WeightOnePointNorm (point)
variable (k : Type u) [Field k] [CharZero k]

/-- The same norm on the genuine universe-lifted representable sections. -/
def largeCycleNorm (q : ℕ) : sections (torusRepresentable k q) (point k) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (MilnorK.K k q)) :=
  AddCommGrpCat.ofHom
    { toFun := fun α => ULift.up (DiagonalPointNorm.cycleValue k q α.down)
      map_zero' := by
        change ULift.up ((DiagonalPointNorm.cycleValue k q) 0) = ULift.up 0
        rw [map_zero]
      map_add' := by
        intro α β
        change ULift.up ((DiagonalPointNorm.cycleValue k q) (α.down + β.down)) =
          ULift.up ((DiagonalPointNorm.cycleValue k q) α.down +
            (DiagonalPointNorm.cycleValue k q) β.down)
        rw [map_add] }

/-- The defining actual relation morphism is annihilated at the field base. -/
theorem relation_largeCycleNorm (q : ℕ) :
    (torusRelation k q).app (op (point k)) ≫ largeCycleNorm k q = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change largeCycleNorm k q ((torusRelation k q).app (op (point k)) s) = 0
  rw [torusRelation_app_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
      change ULift.up (DiagonalPointNorm.cycleValue k (q + 1) (_ ≫
        (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) q i))) = ULift.up 0
      rw [DiagonalFinitePointEvaluation.cycleValue_axis]

/-- The objectwise norm descended through the actual reduced-torus cokernel. -/
def reducedNormLarge (q : ℕ) : sections (reducedTorus k q) (point k) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (MilnorK.K k q)) :=
  (PreservesCokernel.iso
      ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (point k))) (torusRelation k q)).hom ≫
    cokernel.desc ((torusRelation k q).app (op (point k)))
      (largeCycleNorm k q) (relation_largeCycleNorm k q)

/-- This descent extends the original signed cycle norm along the literal quotient map. -/
@[reassoc (attr := simp)] theorem toReducedTorus_reducedNormLarge (q : ℕ) :
    (toReducedTorus k q).hom.app (op (point k)) ≫ reducedNormLarge k q = largeCycleNorm k q := by
  change ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (point k))).map
    (cokernel.π (torusRelation k q)) ≫ _ = _
  rw [reducedNormLarge, PreservesCokernel.π_iso_hom_assoc]
  exact cokernel.π_desc _ _ _

/-- The norm of an actual reduced point section, valued in the original field's units. -/
def reducedNorm (q : ℕ) : sections (reducedTorus k q) (point k) →+ MilnorK.K k q where
  toFun s := (reducedNormLarge k q s).down
  map_zero' := by rw [map_zero]; rfl
  map_add' s t := by rw [map_add]; rfl

variable {k}

/-- The actual quotient retains the original norm formula on every signed cycle. -/
@[simp] theorem reducedNorm_quotient (q : ℕ) (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    reducedNorm k q ((toReducedTorus k q).hom.app (op (point k)) (ULift.up α)) =
      DiagonalPointNorm.cycleValue k q α := by
  have h := ConcreteCategory.congr_hom (toReducedTorus_reducedNormLarge k q) (ULift.up α)
  exact congrArg ULift.down h

/-- Every rational tuple graph retains its literal original Milnor symbol. -/
@[simp] theorem reducedNorm_rationalTuple (q : ℕ) (a : Fin q → kˣ) :
    reducedNorm k q ((toReducedTorus k q).hom.app (op (point k))
      (ULift.up ((Cor.graphFunctor k).map (DiagonalCycleSymbols.rationalTuple k q a)))) =
        MilnorK.symbol a := by
  rw [reducedNorm_quotient, DiagonalPointNorm.cycleValue_rationalTuple]

end Motivic.DiagonalReducedPointNorm
