/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.PointedGermLiftGraph
public import Lean.Util.CollectAxioms

/-! Regression checks for actual graph witnesses on arbitrary original germs. -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
@[expose] public noncomputable section
open CategoryTheory
open Opposite
open AlgebraicGeometry
open Motivic
open _root_.Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.PointedGermLiftGraph
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- Neither an étale map nor a closed source point is required for graph existence. -/
theorem arbitrary_map_witness (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    Nonempty (PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a) :=
  exists_pointedGermLiftWitness_graph k P f x a

/-- Every actual graph witness has the canonical original-fiber pullback value. -/
theorem arbitrary_graph_value
    (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) F)
    (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (L : PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a) :
    L.value k P = SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) :=
  L.value_graph k P hP f x a

/-- Pullback on original point fibers is additive before any sheaf assumption. -/
theorem original_germ_pullback_add (f : X ⟶ Y) (x : X.left)
    (a b : (SmoothSite.nisnevichPointFiberCocone Y (f.left x) F).pt) :
    SmoothSite.originalGermPullback.{u, 0} F f x (a + b) =
      SmoothSite.originalGermPullback.{u, 0} F f x a +
        SmoothSite.originalGermPullback.{u, 0} F f x b := map_add _ _ _

/-- Global-section germs restrict by the original ordinary presheaf map. -/
theorem original_germ_pullback_section (f : X ⟶ Y) (x : X.left)
    (s : (F).obj (op Y)) :
    SmoothSite.originalGermPullback.{u, 0} F f x
        (SmoothSite.sectionToNisnevichPoint.{u, 0} F Y (f.left x) s) =
      SmoothSite.sectionToNisnevichPoint.{u, 0} F X x ((F).map f.op s) :=
  ConcreteCategory.congr_hom
    (SmoothSite.sectionToNisnevichPoint_originalGermPullback.{u, 0} F f x) s

open Lean in
run_cmd do
  for name in #[``arbitrary_map_witness, ``arbitrary_graph_value,
      ``original_germ_pullback_add, ``original_germ_pullback_section,
      ``PointedGermLiftWitness.graphFromRepresentative_value,
      ``pullbackAlongToTarget_center,
      ``FiniteCorrespondenceGenerator.projection_target_of_mem_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual graph witnesses and original-germ pullback: standard foundations only."

end MotivicTest.PointedGermLiftGraph
