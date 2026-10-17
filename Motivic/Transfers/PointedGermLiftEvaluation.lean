/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteRepresentativeFamilyIndependence
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichPointChosenGeneratorLift

/-!
# Actual finite witnesses for evaluation of a germ tuple through a correspondence

This records only the concrete pointed-neighborhood lift diagram and its section
representatives. It assumes no independence, composition, envelope or acyclicity
law. Existence for each original generator follows from actual finite branch lifting.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- A finite actual lift diagram with representatives of an original germ tuple. -/
structure PointedGermLiftWitness (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) where
  source : SmoothSite.NisnevichNeighborhood X x
  size : ℕ
  point : Fin size → Y.left
  target : ∀ i, SmoothSite.NisnevichNeighborhood Y (point i)
  branch : ∀ i, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj source) ⟶
    Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (point i)).obj (target i))
  graph_eq : (∑ i, branch i ≫ (Cor.graphFunctor k).map (target i).toBase) =
    (Cor.graphFunctor k).map source.toBase ≫ δ
  center_control : ∀ i A, A ∈ (branch i).support → ∀ z : A.scheme,
    A.projection z = source.center → A.targetProjection z = (target i).center
  representative : ∀ i, (F).obj
    (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (point i)).obj (target i)))
  represents : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (point i) F).ι.app
    (op (target i)) (representative i) = a (point i)

/-- The value of the concrete diagram is its original source-point cocone value. -/
def PointedGermLiftWitness.value {δ : Cor.mk X ⟶ Cor.mk Y} {x : X.left}
    {a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt}
    (L : PointedGermLiftWitness k P δ x a) : (SmoothSite.nisnevichPointFiberCocone X x F).pt :=
  (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op L.source)
    (∑ i, P.transfer (L.branch i) (L.representative i))

/-- Every original generator admits a finite actual witness at every source
point and every tuple of original target germs. No point is assumed closed. -/
theorem exists_pointedGermLiftWitness
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    Nonempty (PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x a) := by
  classical
  choose R s hs using fun y => SmoothSite.exists_original_germ_representative.{u, 0} F y (a y)
  let V := fun y => (SmoothSite.nisnevichNeighborhoodFunctor Y y).obj (R y)
  let q : ∀ y, V y ⟶ Y := fun y => (R y).toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp only [q]; infer_instance
  obtain ⟨N, n, label, β, hβ, hcontrol⟩ :=
    A.exists_pointed_graph_family_factorization_at_chosen_points k x V q
      (fun y => (R y).center) (by
        intro z _
        exact ⟨A.targetProjection z, (R (A.targetProjection z)).toBase_center, inferInstance⟩)
  exact ⟨{
    source := N
    size := n
    point := label
    target := fun i => R (label i)
    branch := β
    graph_eq := hβ
    center_control := fun i B hB => (hcontrol i B hB).2
    representative := fun i => s (label i)
    represents := fun i => hs (label i) }⟩

end Motivic.PresheafWithTransfers
