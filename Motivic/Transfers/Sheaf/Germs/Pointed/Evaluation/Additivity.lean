/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Independence
public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Simultaneous

/-! # Additivity of actual original-germ evaluation for correspondence generators -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

include hP

/-- Additivity is proved on simultaneous actual finite witnesses, not imposed
on the chosen original-germ evaluation. -/
theorem generatorGermEvaluation_add
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (a b : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    generatorGermEvaluation k P A x (a + b) =
      generatorGermEvaluation k P A x a + generatorGermEvaluation k P A x b := by
  obtain ⟨L, M, N, h⟩ := exists_additive_pointedGermLiftWitnesses k P A x a b
  rw [generatorGermEvaluation_eq_of_witness k P hP A x (a + b) N,
    generatorGermEvaluation_eq_of_witness k P hP A x a L,
    generatorGermEvaluation_eq_of_witness k P hP A x b M]
  exact h

/-- Zero follows from the proved addition identity in the original source fiber. -/
theorem generatorGermEvaluation_zero
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left) :
    generatorGermEvaluation k P A x 0 = 0 := by
  have h := generatorGermEvaluation_add k P hP A x 0 0
  have h' : generatorGermEvaluation k P A x 0 + 0 =
      generatorGermEvaluation k P A x 0 + generatorGermEvaluation k P A x 0 := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

/-- The actual generator action on original germ tuples is an additive homomorphism.
No correspondence-composition or ordinary-cohomology transfer law is asserted here. -/
def generatorGermHom (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left) :
    (∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) →+
      (SmoothSite.nisnevichPointFiberCocone X x F).pt where
  toFun := generatorGermEvaluation k P A x
  map_zero' := generatorGermEvaluation_zero k P hP A x
  map_add' := generatorGermEvaluation_add k P hP A x

end Motivic.PresheafWithTransfers
