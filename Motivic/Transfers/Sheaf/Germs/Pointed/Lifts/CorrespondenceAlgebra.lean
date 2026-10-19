/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Evaluation
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteRepresentativeUnion
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.PointControl
public import Motivic.AlgebraicGeometry.Correspondences.Graph.PostcompositionPointControl

/-!
# Algebra of actual finite lift witnesses in the correspondence variable

The original target germ tuple stays fixed. Addition uses the literal common
source neighborhood and appended target representatives. All value identities
follow from transfer algebra and the original point cocone, without a sheaf
hypothesis or an assumed germ evaluator.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

namespace PointedGermLiftWitness
open _root_.AlgebraicGeometry.Scheme
variable {δ ε : Cor.mk X ⟶ Cor.mk Y} {x : X.left}
  {a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt}

/-- The zero correspondence has the empty finite witness at the identity source. -/
def zero (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    PointedGermLiftWitness k P (0 : Cor.mk X ⟶ Cor.mk Y) x a where
  source := identity X x
  size := 0
  point := by intro i; exact Fin.elim0 i
  target := by intro i; exact Fin.elim0 i
  branch := by intro i; exact Fin.elim0 i
  graph_eq := by simp
  center_control := by intro i; exact Fin.elim0 i
  representative := by intro i; exact Fin.elim0 i
  represents := by intro i; exact Fin.elim0 i

@[simp]
theorem value_zero (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    (zero k P x a).value k P = 0 := by
  simp only [value, zero, Fin.sum_univ_zero]
  exact map_zero ((SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op (identity X x))).hom

/-- Negating the branches leaves their actual support centers and representatives unchanged. -/
def neg (L : PointedGermLiftWitness k P δ x a) :
    PointedGermLiftWitness k P (-δ) x a where
  source := L.source
  size := L.size
  point := L.point
  target := L.target
  branch := fun i => -L.branch i
  graph_eq := by
    simpa only [Preadditive.neg_comp, Finset.sum_neg_distrib,
      Preadditive.comp_neg] using congrArg Neg.neg L.graph_eq
  center_control := by
    intro i A hA
    change A ∈ (-(L.branch i : FiniteCorrespondence _ _)).support at hA
    rw [Finsupp.support_neg] at hA
    exact L.center_control i A hA
  representative := L.representative
  represents := L.represents

@[simp]
theorem value_neg (L : PointedGermLiftWitness k P δ x a) :
    (L.neg k P).value k P = -L.value k P := by
  have hn : ∀ i, P.transfer (-L.branch i) (L.representative i) =
      -P.transfer (L.branch i) (L.representative i) := by
    intro i
    rw [transfer_neg]
    rfl
  change (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op L.source)
    (∑ i, P.transfer (-L.branch i) (L.representative i)) = _
  rw [Finset.sum_congr rfl (fun i _ => hn i), Finset.sum_neg_distrib]
  exact map_neg ((SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op L.source)).hom _

/-- An actual pointed source refinement preserves the witness and its target representatives. -/
def refine (L : PointedGermLiftWitness k P δ x a)
    (N : SmoothSite.NisnevichNeighborhood X x) (f : N ⟶ L.source) :
    PointedGermLiftWitness k P δ x a where
  source := N
  size := L.size
  point := L.point
  target := L.target
  branch := fun i => (Cor.graphFunctor k).map
    ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f) ≫ L.branch i
  graph_eq := by
    change (∑ i, ((Cor.graphFunctor k).map
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f) ≫ L.branch i) ≫
        (Cor.graphFunctor k).map (L.target i).toBase) = _
    simp_rw [Category.assoc]
    rw [← Preadditive.comp_sum, L.graph_eq, ← Category.assoc,
      ← Functor.map_comp, map_toBase]
  center_control := by
    intro i A hA z hz
    exact FiniteCorrespondence.target_eq_of_mem_flat_graph_comp (L.branch i)
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f) L.source.center N.center
      (map_center f) (L.target i).center (L.center_control i) A hA z hz
  representative := L.representative
  represents := L.represents

/-- Refinement does not change the original source point value. -/
theorem value_refine (L : PointedGermLiftWitness k P δ x a)
    (N : SmoothSite.NisnevichNeighborhood X x) (f : N ⟶ L.source) :
    (L.refine k P N f).value k P = L.value k P := by
  have h := (SmoothSite.nisnevichPointFiberCocone X x F).w f.op
  change (F).map ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f).op ≫
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N) =
      (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op L.source) at h
  have hv := ConcreteCategory.congr_hom h
    (∑ i, P.transfer (L.branch i) (L.representative i))
  change (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N)
    (∑ i, P.transfer ((Cor.graphFunctor k).map
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f) ≫ L.branch i)
        (L.representative i)) = _
  simp only [transfer_comp, ConcreteCategory.comp_apply]
  change (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N)
    (∑ i, (F).map ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f).op
      (P.transfer (L.branch i) (L.representative i))) = _
  rw [← map_sum ((F).map ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f).op).hom]
  exact hv


theorem center_control_refine_postcomp (L : PointedGermLiftWitness k P δ x a)
    (N : SmoothSite.NisnevichNeighborhood X x) (f : N ⟶ L.source) (i : Fin L.size)
    {V : SmoothSite (Spec (.of k))}
    (e : (SmoothSite.nisnevichNeighborhoodFunctor Y (L.point i)).obj (L.target i) ⟶ V)
    (v : V.left) (he : e.left (L.target i).center = v)
    (A : FiniteCorrespondenceGenerator
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom V.hom)
    (hA : A ∈ (((Cor.graphFunctor k).map
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f) ≫ L.branch i) ≫
        (Cor.graphFunctor k).map e).support)
    (z : A.scheme) (hz : A.projection z = N.center) : A.targetProjection z = v := by
  obtain ⟨B, hB, b, hs, ht⟩ :=
    FiniteCorrespondence.exists_support_point_lift_of_mem_comp_graph
      ((Cor.graphFunctor k).map ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f) ≫
        L.branch i) e A hA z
  have hb := FiniteCorrespondence.target_eq_of_mem_flat_graph_comp
    (L.branch i) ((SmoothSite.nisnevichNeighborhoodFunctor X x).map f)
    L.source.center N.center (map_center f) (L.target i).center
    (L.center_control i) B hB b (hs.trans hz)
  exact ht.symm.trans ((congrArg e.left hb).trans he)

/-- Addition of signed correspondences at the same original target germ tuple. -/
def add (L : PointedGermLiftWitness k P δ x a)
    (M : PointedGermLiftWitness k P ε x a) :
    PointedGermLiftWitness k P (δ + ε) x a := by
  classical
  let N := common L.source M.source
  let f : (SmoothSite.nisnevichNeighborhoodFunctor X x).obj N ⟶
      (SmoothSite.nisnevichNeighborhoodFunctor X x).obj L.source :=
    (SmoothSite.nisnevichNeighborhoodFunctor X x).map (commonFst L.source M.source)
  let g : (SmoothSite.nisnevichNeighborhoodFunctor X x).obj N ⟶
      (SmoothSite.nisnevichNeighborhoodFunctor X x).obj M.source :=
    (SmoothSite.nisnevichNeighborhoodFunctor X x).map (commonSnd L.source M.source)
  let R := appendFamily L.point L.target M.point M.target
  let e := appendLeftIso L.point L.target M.point M.target
  let e' := appendRightIso L.point L.target M.point M.target
  let β : ∀ i : Fin L.size,
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (appendObjects L.point L.target M.point M.target (Fin.castAdd M.size i)) :=
    fun i => ((Cor.graphFunctor k).map f ≫ L.branch i) ≫ (Cor.graphFunctor k).map (e i).hom
  let β' : ∀ j : Fin M.size,
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (appendObjects L.point L.target M.point M.target (Fin.natAdd L.size j)) :=
    fun j => ((Cor.graphFunctor k).map g ≫ M.branch j) ≫ (Cor.graphFunctor k).map (e' j).hom
  refine {
    source := N
    size := L.size + M.size
    point := appendPoints L.point L.target M.point M.target
    target := R
    branch := Fin.addCases (motive := fun l =>
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (appendObjects L.point L.target M.point M.target l)) β β'
    graph_eq := ?_
    center_control := ?_
    representative := appendSections.{u, 0} L.point L.target M.point M.target F
      L.representative M.representative
    represents := appendSections_represents.{u, 0} L.point L.target M.point M.target F
      L.representative M.representative a L.represents M.represents }
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, β, β', Category.assoc,
      ← Functor.map_comp, e, e', R, appendLeftIso_hom_toBase,
      appendRightIso_hom_toBase]
    rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, L.graph_eq, M.graph_eq,
      ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    simp only [f, g, map_toBase, Preadditive.comp_add]
  · apply Fin.addCases
    · intro i A hA z hz
      simp only [Fin.addCases_left] at hA
      exact center_control_refine_postcomp k P L N (commonFst L.source M.source) i
        (e i).hom _ (appendLeftIso_hom_center L.point L.target M.point M.target i)
        A hA z hz
    · intro j A hA z hz
      simp only [Fin.addCases_right] at hA
      exact center_control_refine_postcomp k P M N (commonSnd L.source M.source) j
        (e' j).hom _ (appendRightIso_hom_center L.point L.target M.point M.target j)
        A hA z hz


theorem append_transfer_sum (L : PointedGermLiftWitness k P δ x a)
    (M : PointedGermLiftWitness k P ε x a) {U : SmoothSite (Spec (.of k))}
    (α : ∀ i, Cor.mk U ⟶
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (L.point i)).obj (L.target i)))
    (α' : ∀ j, Cor.mk U ⟶
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (M.point j)).obj (M.target j))) :
    (∑ l, P.transfer (Fin.addCases (motive := fun l =>
      Cor.mk U ⟶ Cor.mk (appendObjects L.point L.target M.point M.target l))
      (fun i => α i ≫ (Cor.graphFunctor k).map
        (appendLeftIso L.point L.target M.point M.target i).hom)
      (fun j => α' j ≫ (Cor.graphFunctor k).map
        (appendRightIso L.point L.target M.point M.target j).hom) l)
      (appendSections.{u, 0} L.point L.target M.point M.target F
        L.representative M.representative l)) =
      (∑ i, P.transfer (α i) (L.representative i)) +
        ∑ j, P.transfer (α' j) (M.representative j) := by
  classical
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [transfer_comp]
    change P.transfer (α i) ((F).map
      (appendLeftIso L.point L.target M.point M.target i).hom.op
      (appendSections L.point L.target M.point M.target F
        L.representative M.representative (Fin.castAdd M.size i))) = _
    rw [appendSections_left.{u, 0}]
  · apply Finset.sum_congr rfl
    intro j _
    rw [transfer_comp]
    change P.transfer (α' j) ((F).map
      (appendRightIso L.point L.target M.point M.target j).hom.op
      (appendSections L.point L.target M.point M.target F
        L.representative M.representative (Fin.natAdd L.size j))) = _
    rw [appendSections_right.{u, 0}]

/-- The concrete appended witness adds source values in the correspondence variable. -/
@[simp]
theorem value_add (L : PointedGermLiftWitness k P δ x a)
    (M : PointedGermLiftWitness k P ε x a) :
    (L.add k P M).value k P = L.value k P + M.value k P := by
  classical
  let N := common L.source M.source
  let f : (SmoothSite.nisnevichNeighborhoodFunctor X x).obj N ⟶
      (SmoothSite.nisnevichNeighborhoodFunctor X x).obj L.source :=
    (SmoothSite.nisnevichNeighborhoodFunctor X x).map (commonFst L.source M.source)
  let g : (SmoothSite.nisnevichNeighborhoodFunctor X x).obj N ⟶
      (SmoothSite.nisnevichNeighborhoodFunctor X x).obj M.source :=
    (SmoothSite.nisnevichNeighborhoodFunctor X x).map (commonSnd L.source M.source)
  let e := appendLeftIso L.point L.target M.point M.target
  let e' := appendRightIso L.point L.target M.point M.target
  let β : ∀ i : Fin L.size,
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (appendObjects L.point L.target M.point M.target (Fin.castAdd M.size i)) :=
    fun i => ((Cor.graphFunctor k).map f ≫ L.branch i) ≫ (Cor.graphFunctor k).map (e i).hom
  let β' : ∀ j : Fin M.size,
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (appendObjects L.point L.target M.point M.target (Fin.natAdd L.size j)) :=
    fun j => ((Cor.graphFunctor k).map g ≫ M.branch j) ≫ (Cor.graphFunctor k).map (e' j).hom
  let s := appendSections.{u, 0} L.point L.target M.point M.target F
    L.representative M.representative
  change (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N)
    (∑ l, P.transfer (Fin.addCases (motive := fun l =>
      Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (appendObjects L.point L.target M.point M.target l)) β β' l) (s l)) = _
  rw [append_transfer_sum k P L M
    (fun i => (Cor.graphFunctor k).map f ≫ L.branch i)
    (fun j => (Cor.graphFunctor k).map g ≫ M.branch j)]
  rw [map_add ((SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N)).hom]
  exact congrArg₂ (· + ·) (L.value_refine k P N (commonFst L.source M.source))
    (M.value_refine k P N (commonSnd L.source M.source))

end PointedGermLiftWitness
end Motivic.PresheafWithTransfers
