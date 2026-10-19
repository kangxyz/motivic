/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.FiniteRepresentatives.LiftIndependence
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.PointControl
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.CommonRefinement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Refinement

/-!
# Independence of the actual source neighborhood for fixed representatives

Two controlled lifts on different pointed source neighborhoods are compared on
their actual common pullback. Flat graph precomposition preserves their target
center controls, and the original point-fiber cocone transports the resulting
center-germ equality back to the two original representatives.

The target representative family is fixed. Neither common finite support nor a
new point-fiber or transfer-envelope structure is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

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
theorem transfer_cocone_eq_of_finite_representatives_common_source
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
  let C := SmoothSite.NisnevichNeighborhood.common N M
  let f := (SmoothSite.nisnevichNeighborhoodFunctor X x).map
    (SmoothSite.NisnevichNeighborhood.commonFst N M)
  let g := (SmoothSite.nisnevichNeighborhoodFunctor X x).map
    (SmoothSite.NisnevichNeighborhood.commonSnd N M)
  let β := (Cor.graphFunctor k).map f ≫ α
  let β' := (Cor.graphFunctor k).map g ≫ α'
  have hfbase : f ≫ N.toBase = C.toBase :=
    SmoothSite.NisnevichNeighborhood.map_toBase
      (SmoothSite.NisnevichNeighborhood.commonFst N M)
  have hgbase : g ≫ M.toBase = C.toBase :=
    SmoothSite.NisnevichNeighborhood.map_toBase
      (SmoothSite.NisnevichNeighborhood.commonSnd N M)
  have heq : β ≫ (Cor.graphFunctor k).map q = β' ≫ (Cor.graphFunctor k).map q := by
    dsimp only [β, β']
    rw [Category.assoc, hα, ← Category.assoc, ← Functor.map_comp, hfbase,
      Category.assoc, hα', ← Category.assoc, ← Functor.map_comp, hgbase]
  have hβ : ∀ A ∈ β.support, ∀ b : A.scheme, A.projection b = C.center →
      A.targetProjection b ∈ T :=
    FiniteCorrespondence.target_mem_of_mem_flat_graph_comp α f N.center C.center
      (SmoothSite.NisnevichNeighborhood.map_center
        (SmoothSite.NisnevichNeighborhood.commonFst N M)) T hfirst
  have hβ' : ∀ A ∈ β'.support, ∀ b : A.scheme, A.projection b = C.center →
      A.targetProjection b ∈ T :=
    FiniteCorrespondence.target_mem_of_mem_flat_graph_comp α' g M.center C.center
      (SmoothSite.NisnevichNeighborhood.map_center
        (SmoothSite.NisnevichNeighborhood.commonSnd N M)) T hfirst'
  have hcenter := transfer_germ_eq_of_finite_representatives_auto_support
    k P y R β β' heq C.center hβ hβ' a s hs
  have hC := SmoothSite.nisnevichPointFiberCocone_eq_of_center_germ_eq F C
    (P.transfer β s) (P.transfer β' s) hcenter
  have hf := (SmoothSite.nisnevichPointFiberCocone X x F).w
    (SmoothSite.NisnevichNeighborhood.commonFst N M).op
  have hg := (SmoothSite.nisnevichPointFiberCocone X x F).w
    (SmoothSite.NisnevichNeighborhood.commonSnd N M).op
  change (F).map f.op ≫ (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op C) =
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N) at hf
  change (F).map g.op ≫ (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op C) =
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op M) at hg
  have htransfer : P.transfer β s = (F).map f.op (P.transfer α s) := by
    dsimp only [β]
    rw [transfer_comp, ConcreteCategory.comp_apply]
    rfl
  have htransfer' : P.transfer β' s = (F).map g.op (P.transfer α' s) := by
    dsimp only [β']
    rw [transfer_comp, ConcreteCategory.comp_apply]
    rfl
  rw [htransfer, htransfer'] at hC
  exact (ConcreteCategory.congr_hom hf (P.transfer α s)).symm.trans
    (hC.trans (ConcreteCategory.congr_hom hg (P.transfer α' s)))

end Motivic.PresheafWithTransfers
