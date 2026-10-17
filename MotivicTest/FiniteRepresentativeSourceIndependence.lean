/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteRepresentativeSourceIndependence
public import Lean.Util.CollectAxioms

/-!
# Original point-fiber independence across actual source neighborhoods

The regression supplies only the original lifts, their original graph equations,
actual center controls and a fixed finite representative tuple. It supplies no
common support, common source, Čech matching or substitute point-fiber structure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace MotivicTest.FiniteRepresentativeSourceIndependence

open Motivic Motivic.PresheafWithTransfers

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))} {n : ℕ} (y : Fin n → Y.left)
  (R : ∀ i, SmoothSite.NisnevichNeighborhood Y (y i))

set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
set_option quotPrecheck false in
local notation "V" => (fun i => (SmoothSite.nisnevichNeighborhoodFunctor Y (y i)).obj (R i))
set_option quotPrecheck false in
local notation "W" => (SmoothSite.finiteCoproduct V)
set_option quotPrecheck false in
local notation "q" => (SmoothSite.finiteCoproductDesc (fun i => (R i).toBase))
set_option quotPrecheck false in
local notation "T" => (Set.range (fun i => (SmoothSite.finiteCoproductι V i).left (R i).center))

/-- Lifts of one correspondence on different actual source neighborhoods give
the same original source-point class for a fixed finite target representative
family. The common source, support and matching Čech germs are all constructed. -/
theorem actual_source_neighborhood_independence
    (x : X.left) (N M : SmoothSite.NisnevichNeighborhood X x)
    (δ : Cor.mk X ⟶ Cor.mk Y)
    (α : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶ Cor.mk W)
    (α' : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj M) ⟶ Cor.mk W)
    (hα : α ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map N.toBase ≫ δ)
    (hα' : α' ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map M.toBase ≫ δ)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = N.center →
      A.targetProjection a ∈ T)
    (hfirst' : ∀ A ∈ α'.support, ∀ a : A.scheme, A.projection a = M.center →
      A.targetProjection a ∈ T)
    (a : ∀ z : Y.left, (SmoothSite.nisnevichPointFiberCocone Y z F).pt)
    (s : P.sections (Cor.mk W))
    (hs : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (y i) F).ι.app (op (R i))
      ((F).map (SmoothSite.finiteCoproductι V i).op s) = a (y i)) :
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N) (P.transfer α s) =
      (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op M) (P.transfer α' s) := by
  exact transfer_cocone_eq_of_finite_representatives_common_source
    k P y R x N M δ α α' hα hα' hfirst hfirst' a s hs

open Lean in
run_cmd do
  for name in #[``actual_source_neighborhood_independence,
      ``transfer_cocone_eq_of_finite_representatives_common_source,
      ``FiniteCorrespondence.target_mem_of_mem_flat_graph_comp,
      ``SmoothSite.nisnevichPointFiberCocone_eq_of_center_germ_eq] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original source-neighborhood lift independence: standard foundations only."

end MotivicTest.FiniteRepresentativeSourceIndependence
