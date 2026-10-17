/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FixedLiftGermIndependence
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichPointNormalizedLift
public import Lean.Util.CollectAxioms

/-! # Single-center locality and actual constructed fixed-lift consumers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic

universe u v

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))}

example (α : FiniteCorrespondence X.hom Y.hom) (x : X.left) (y : Y.left)
    (hα : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x → A.targetProjection z = y)
    (s t : P.sections (Cor.mk Y))
    (hst : SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P) Y y s =
      SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P) Y y t) :
    SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
        X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
        X x (P.transfer α t) :=
  PresheafWithTransfers.transfer_germ_eq_of_single_center k P α x y hα s t hst

/-- Apply the actual normalized construction first, then prove independence
for every pair of section representatives on its resulting target neighborhoods. -/
example (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (T : Set Y.left) (hT : T.Finite) (hclosed : ∀ y ∈ T, IsClosed ({y} : Set Y.left))
    (hAT : ∀ a : A.scheme, A.projection a = x → A.targetProjection a ∈ T)
    (R : ∀ y : T, SmoothSite.NisnevichNeighborhood Y y.val) :
    ∃ (M : ∀ y : T, SmoothSite.NisnevichNeighborhood Y y.val)
      (_ρ : ∀ y, M y ⟶ R y) (N : SmoothSite.NisnevichNeighborhood X x)
      (n : ℕ) (label : Fin n → T)
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (M (label j)))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (M (label j)).toBase) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ s t : ∀ j, P.sections
          (Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (M (label j)))),
        (∀ j, SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
            ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (M (label j)))
            (M (label j)).center (s j) =
          SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
            ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (M (label j)))
            (M (label j)).center (t j)) →
        (SmoothSite.nisnevichPointFiberCocone X x
            ((PresheafWithTransfers.toPresheaf k).obj P)).ι.app (op N)
            (∑ j, P.transfer (β j) (s j)) =
          (SmoothSite.nisnevichPointFiberCocone X x
            ((PresheafWithTransfers.toPresheaf k).obj P)).ι.app (op N)
            (∑ j, P.transfer (β j) (t j)) := by
  obtain ⟨M, ρ, N, n, label, β, _, hβ, hbranch⟩ :=
    A.exists_normalized_pointed_graph_family_factorization k x T hT hclosed hAT R
  refine ⟨M, ρ, N, n, label, β, hβ, ?_⟩
  intro s t hst
  exact PresheafWithTransfers.fixed_lift_germ_evaluation_eq k P x N n
    (fun j ↦ (SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (M (label j)))
    (fun j ↦ (M (label j)).center) β hbranch s t hst

open Lean Motivic.PresheafWithTransfers in
run_cmd do
  for name in #[``generator_transfer_germ_eq_zero_of_single_center,
      ``transfer_germ_eq_zero_of_single_center, ``transfer_germ_eq_of_single_center,
      ``fixed_lift_germ_evaluation_eq] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual fixed lifts depend only on designated center germs, at arbitrary source points."
