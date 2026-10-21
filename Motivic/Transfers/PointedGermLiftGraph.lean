/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Independence
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.Pullback

/-!
# Pointed graph lifts for presheaves with transfers
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
/-- The Noetherian instance used in this module. -/
local instance transfersPointedGermLiftGraphNoetherian
    {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsNoetherian T.left)
/-- The reduced scheme instance used in this module. -/
local instance transfersPointedGermLiftGraphReduced
    {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsReduced T.left)
variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- Every generator surviving in an actual graph satisfies the graph equation. -/
theorem projection_target_of_mem_graph (f : X ⟶ Y)
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (hA : A ∈ ((Cor.graphFunctor k).map f).support) :
    A.projection ≫ f.left = A.targetProjection := by
  classical
  change A ∈ (componentGraphCycleOver f.left (MorphismProperty.Over.w f)).support at hA
  rw [componentGraphCycleOver_eq_sum] at hA
  obtain ⟨C, hC, hA⟩ := Finsupp.mem_support_finsetSum A hA
  have hC' : C ∈ irreducibleComponents X.left := by simpa using hC
  rw [dite_eq_left hC'] at hA
  have h := Finsupp.support_single_subset hA
  have h' : A = componentGraphGeneratorOver f.left (MorphismProperty.Over.w f) C hC' :=
    Finset.mem_singleton.mp h
  subst A
  exact componentGraphGeneratorOver_projection_target _ _ _ _

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

/-- A representative of just the germ at the image point gives an actual
one-branch graph witness, even on a disconnected source. -/
def PointedGermLiftWitness.graphFromRepresentative (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (N : SmoothSite.NisnevichNeighborhood Y (f.left x))
    (s : (F).obj (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (f.left x)).obj N)))
    (hs : (SmoothSite.nisnevichPointFiberCocone Y (f.left x) F).ι.app (op N) s = a (f.left x)) :
    PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a where
  source := pullbackAlong f x N
  size := 1
  point := fun _ => f.left x
  target := fun _ => N
  branch := fun _ => (Cor.graphFunctor k).map (pullbackAlongToTarget f x N)
  graph_eq := by simp only [Fin.sum_univ_one, ← Functor.map_comp, pullbackAlongToTarget_toBase]
  center_control := by
    intro i A hA z hz
    have h := congrArg (fun g => g z) (A.projection_target_of_mem_graph
      (pullbackAlongToTarget f x N) hA)
    change (pullbackAlongToTarget f x N).left (A.projection z) = A.targetProjection z at h
    exact h.symm.trans
      ((congrArg (fun t => (pullbackAlongToTarget f x N).left t) hz).trans
        (pullbackAlongToTarget_center f x N))
  representative := fun _ => s
  represents := fun _ => hs

/-- The one-branch actual graph witness evaluates to pullback of the given
original target germ, using the colimit-induced map rather than an assumed law. -/
theorem PointedGermLiftWitness.graphFromRepresentative_value (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (N : SmoothSite.NisnevichNeighborhood Y (f.left x))
    (s : (F).obj (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (f.left x)).obj N)))
    (hs : (SmoothSite.nisnevichPointFiberCocone Y (f.left x) F).ι.app (op N) s = a (f.left x)) :
    (PointedGermLiftWitness.graphFromRepresentative k P f x a N s hs).value k P =
      SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) := by
  have h := ConcreteCategory.congr_hom (SmoothSite.originalGermPullback_ι.{u, 0} F f x N) s
  rw [ConcreteCategory.comp_apply, hs, ConcreteCategory.comp_apply] at h
  change (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op (pullbackAlong f x N))
      (∑ _ : Fin 1, P.transfer ((Cor.graphFunctor k).map (pullbackAlongToTarget f x N)) s) = _
  rw [Fin.sum_univ_one]
  exact h.symm

/-- Every tuple of original germs admits an actual graph witness. -/
theorem exists_pointedGermLiftWitness_graph (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    Nonempty (PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a) := by
  obtain ⟨N, s, hs⟩ := SmoothSite.exists_original_germ_representative.{u, 0} F
    (f.left x) (a (f.left x))
  exact ⟨PointedGermLiftWitness.graphFromRepresentative k P f x a N s hs⟩

/-- For an ordinary Nisnevich sheaf, every actual graph witness has the
canonical pullback value on the original germ at the image point. -/
theorem PointedGermLiftWitness.value_graph
    (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) F)
    (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (L : PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a) :
    L.value k P = SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) := by
  obtain ⟨N, s, hs⟩ := SmoothSite.exists_original_germ_representative.{u, 0} F
    (f.left x) (a (f.left x))
  exact (L.value_eq k P hP
    (PointedGermLiftWitness.graphFromRepresentative k P f x a N s hs)).trans
      (PointedGermLiftWitness.graphFromRepresentative_value k P f x a N s hs)

end Motivic.PresheafWithTransfers
