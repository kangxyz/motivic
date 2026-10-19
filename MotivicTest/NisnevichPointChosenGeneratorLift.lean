/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Points.ChosenGeneratorLift
public import Motivic.Transfers.Sheaf.Germs.FixedLiftIndependence
public import Lean.Util.CollectAxioms

/-! # Chosen branch values at arbitrary and specializing target centers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic

universe u v

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- The selected target centers may specialize strictly: one is proved
nonclosed, yet the actual chosen neighborhood centers control every branch. -/
example (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (y₀ y₁ : Y.left) (hsp : y₀ ⤳ y₁) (hne : y₀ ≠ y₁)
    (hAT : ∀ a : A.scheme, A.projection a = x → A.targetProjection a ∈ ({y₀, y₁} : Set Y.left))
    (R : ∀ y : ({y₀, y₁} : Set Y.left), SmoothSite.NisnevichNeighborhood Y y.val) :
    ¬ IsClosed ({y₀} : Set Y.left) ∧
    ∃ (N : SmoothSite.NisnevichNeighborhood X x) (n : ℕ)
      (label : Fin n → ({y₀, y₁} : Set Y.left))
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (R (label j)))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (R (label j)).toBase) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support → ∀ z : B.scheme, B.projection z = N.center →
        B.targetProjection z = (R (label j)).center := by
  refine ⟨?_, A.exists_pointed_germ_family_factorization k x {y₀, y₁} hAT R⟩
  intro hc
  exact hne (Set.mem_singleton_iff.mp (hsp.mem_closed hc (Set.mem_singleton y₀))).symm

/-- Construct the finite lift from arbitrary chosen target neighborhoods,
then prove its evaluations agree on equal designated germs. No point or
selected set is assumed closed, and no refinement of R is required. -/
example (P : PresheafWithTransfers.{max (u + 1) v} k)
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (T : Set Y.left)
    (hAT : ∀ a : A.scheme, A.projection a = x → A.targetProjection a ∈ T)
    (R : ∀ y : T, SmoothSite.NisnevichNeighborhood Y y.val) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x) (n : ℕ) (label : Fin n → T)
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (R (label j)))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (R (label j)).toBase) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ s t : ∀ j, P.sections
          (Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (R (label j)))),
        (∀ j, SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
            ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (R (label j)))
            (R (label j)).center (s j) =
          SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
            ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (R (label j)))
            (R (label j)).center (t j)) →
        (SmoothSite.nisnevichPointFiberCocone X x
            ((PresheafWithTransfers.toPresheaf k).obj P)).ι.app (op N)
            (∑ j, P.transfer (β j) (s j)) =
          (SmoothSite.nisnevichPointFiberCocone X x
            ((PresheafWithTransfers.toPresheaf k).obj P)).ι.app (op N)
            (∑ j, P.transfer (β j) (t j)) := by
  obtain ⟨N, n, label, β, hβ, hbranch⟩ :=
    A.exists_pointed_germ_family_factorization k x T hAT R
  refine ⟨N, n, label, β, hβ, ?_⟩
  intro s t hst
  exact PresheafWithTransfers.fixed_lift_germ_evaluation_eq k P x N n
    (fun j ↦ (SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (R (label j)))
    (fun j ↦ (R (label j)).center) β hbranch s t hst

open Lean Motivic.FiniteCorrespondenceGenerator in
run_cmd do
  for name in #[``exists_pointed_graph_family_factorization_at_chosen_points,
      ``exists_pointed_germ_family_factorization] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual branch control and fixed-lift independence allow specializing target points."
