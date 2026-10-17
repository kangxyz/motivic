/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.PointedGermEvaluationSigned
public import Motivic.Transfers.PointedGermLiftCorrespondenceAlgebra

/-! # Actual finite witnesses compute the signed correspondence evaluation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}

/-- A concrete witness whose original-colimit value is the signed evaluation. -/
def HasComputingPointedGermLift (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left,
      (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt) : Prop :=
  ∃ L : PointedGermLiftWitness k P δ x a,
    L.value k P = correspondenceGermHom k P hP x δ a

namespace HasComputingPointedGermLift
variable (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt)
include a

theorem zero : HasComputingPointedGermLift k P hP (0 : Cor.mk X ⟶ Cor.mk Y) x a := by
  refine ⟨PointedGermLiftWitness.zero k P x a, ?_⟩
  rw [PointedGermLiftWitness.value_zero, map_zero, AddMonoidHom.zero_apply]

theorem add (δ ε : Cor.mk X ⟶ Cor.mk Y)
    (hδ : HasComputingPointedGermLift k P hP δ x a)
    (hε : HasComputingPointedGermLift k P hP ε x a) :
    HasComputingPointedGermLift k P hP (δ + ε) x a := by
  obtain ⟨L, hL⟩ := hδ
  obtain ⟨M, hM⟩ := hε
  refine ⟨L.add k P M, ?_⟩
  rw [PointedGermLiftWitness.value_add, hL, hM, map_add, AddMonoidHom.add_apply]

theorem neg (δ : Cor.mk X ⟶ Cor.mk Y)
    (hδ : HasComputingPointedGermLift k P hP δ x a) :
    HasComputingPointedGermLift k P hP (-δ) x a := by
  obtain ⟨L, hL⟩ := hδ
  refine ⟨L.neg k P, ?_⟩
  rw [PointedGermLiftWitness.value_neg, hL, map_neg, AddMonoidHom.neg_apply]

theorem cycle (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
    HasComputingPointedGermLift k P hP (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x a := by
  obtain ⟨L⟩ := exists_pointedGermLiftWitness k P A x a
  refine ⟨L, ?_⟩
  rw [correspondenceGermHom_cycle]
  exact (generatorGermEvaluation_eq_of_witness k P hP A x a L).symm

theorem single (A : FiniteCorrespondenceGenerator X.hom Y.hom) (m : ℤ) :
    HasComputingPointedGermLift k P hP (show Cor.mk X ⟶ Cor.mk Y from Finsupp.single A m)
      x a := by
  induction m using Int.induction_on with
  | zero => simpa only [Finsupp.single_zero] using zero k P hP x a
  | succ n ih =>
    simpa only [Finsupp.single_add, FiniteCorrespondenceGenerator.cycle] using
      add k P hP x a (Finsupp.single A (n : ℤ)) A.cycle ih (cycle k P hP x a A)
  | pred n ih =>
    simpa only [sub_eq_add_neg, Finsupp.single_add, Finsupp.single_neg,
      FiniteCorrespondenceGenerator.cycle] using
      add k P hP x a (Finsupp.single A (-(n : ℤ))) (-A.cycle) ih
        (neg k P hP x a A.cycle (cycle k P hP x a A))

end HasComputingPointedGermLift

/-- Every signed correspondence admits a genuine finite witness computing its
signed evaluation. The construction uses actual common sources and finite unions. -/
theorem exists_signed_pointedGermLiftWitness
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt) :
    ∃ L : PointedGermLiftWitness k P δ x a,
      L.value k P = correspondenceGermHom k P hP x δ a :=
  Finsupp.induction_linear δ (HasComputingPointedGermLift.zero k P hP x a)
    (HasComputingPointedGermLift.add k P hP x a)
    (HasComputingPointedGermLift.single k P hP x a)

/-- No choice of actual source, targets, branches, or representatives changes the
signed evaluation in the original source-point colimit. -/
theorem correspondenceGermHom_eq_of_witness
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt)
    (L : PointedGermLiftWitness k P δ x a) :
    correspondenceGermHom k P hP x δ a = L.value k P := by
  obtain ⟨M, hM⟩ := exists_signed_pointedGermLiftWitness k P hP δ x a
  exact hM.symm.trans (M.value_eq k P hP L)

end Motivic.PresheafWithTransfers
