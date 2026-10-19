/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Points.NormalizedLift
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.Fibers.ClosedCentersFiniteSupport
public import Lean.Util.CollectAxioms

/-! # Actual finite-center representatives and controlled correspondence branches -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (x : X.left) (hx : IsClosed ({x} : Set X.left))

/-- The selected set is exactly the actual finite support's target fiber. The
input representatives are arbitrary and the output refines those same representatives. -/
example (R : ∀ y : A.targetProjection '' (A.projection ⁻¹' {x}),
    SmoothSite.NisnevichNeighborhood Y y.val) :
    ∃ (M : ∀ y : A.targetProjection '' (A.projection ⁻¹' {x}),
        SmoothSite.NisnevichNeighborhood Y y.val)
      (ρ : ∀ y, M y ⟶ R y) (N : SmoothSite.NisnevichNeighborhood X x)
      (n : ℕ) (label : Fin n → A.targetProjection '' (A.projection ⁻¹' {x}))
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (M (label j)))),
      (∀ y, (M y).obj.val.left ≫ (ρ y).hom.hom.left = (R y).obj.val.left) ∧
      (∑ j, β j ≫ (Cor.graphFunctor k).map (M (label j)).toBase) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support →
        B.targetProjection '' (B.projection ⁻¹' {N.center}) ⊆ {(M (label j)).center} := by
  let T : Set Y.left := A.targetProjection '' (A.projection ⁻¹' {x})
  have hT : T.Finite := (A.projection.finite_preimage_singleton x).image _
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace
    (Y := Spec (.of k)) (show Y.left ⟶ Spec (.of k) from Y.hom)
  have hclosed : ∀ y ∈ T, IsClosed ({y} : Set Y.left) := by
    rintro y ⟨a, ha, rfl⟩
    change A.projection a = x at ha
    exact Scheme.Hom.isClosed_target_of_locallyQuasiFinite_source (Y := Y.left)
      A.projection A.targetProjection a (ha.symm ▸ hx)
  obtain ⟨M, ρ, N, n, label, β, hM, hβ, hbranch⟩ :=
    A.exists_normalized_pointed_graph_family_factorization k x T hT hclosed
      (fun a ha ↦ ⟨a, ha, rfl⟩) R
  refine ⟨M, ρ, N, n, label, β, fun y ↦ (hM y).2.2.1, hβ, ?_⟩
  intro j B hB y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact hbranch j B hB z hz

open Lean Motivic.FiniteCorrespondenceGenerator in
run_cmd do
  for name in #[``exists_pointed_graph_family_factorization_with_support,
      ``target_eq_center_of_support_lift,
      ``exists_normalized_pointed_graph_family_factorization] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Normalized chosen representatives retain exact source-fiber branch control."
