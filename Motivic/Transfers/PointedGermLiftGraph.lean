/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.PointedGermLiftIndependence

/-!
# Actual graph witnesses on arbitrary original Nisnevich germs

Pulling back a pointed étale neighborhood along an arbitrary smooth-site map
uses its actual residue-field map. Its graph gives a one-branch finite witness,
with every surviving support point above the chosen source center sent to the
chosen target center. Neither the map nor the point is assumed étale or closed.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v

namespace Motivic.SmoothSite.NisnevichNeighborhood
variable {S : Scheme.{u}} {X Y : SmoothSite S} (f : X ⟶ Y) (x : X.left)

/-- The target neighborhood's original point after the actual residue-field map. -/
def pullbackAlongTargetPoint (N : NisnevichNeighborhood Y (f.left x)) :
    Spec (X.left.residueField x) ⟶ N.obj.obj.left :=
  Spec.map (f.left.residueFieldMap x) ≫ N.obj.val.left

@[reassoc]
theorem pullbackAlongTargetPoint_toBase (N : NisnevichNeighborhood Y (f.left x)) :
    pullbackAlongTargetPoint f x N ≫ N.toBase.left =
      X.left.fromSpecResidueField x ≫ f.left := by
  have hN : N.obj.val.left ≫ N.toBase.left =
      Y.left.fromSpecResidueField (f.left x) := Over.w N.obj.val
  rw [pullbackAlongTargetPoint, Category.assoc, hN]
  exact f.left.SpecMap_residueFieldMap_fromSpecResidueField x

/-- The literal residue-field point of the scheme pullback. -/
def pullbackAlongPoint (N : NisnevichNeighborhood Y (f.left x)) :
    Spec (X.left.residueField x) ⟶ pullback N.toBase.left f.left :=
  pullback.lift (pullbackAlongTargetPoint f x N) (X.left.fromSpecResidueField x)
    (pullbackAlongTargetPoint_toBase f x N)

/-- An actual pointed neighborhood pulled back along an arbitrary smooth-site map. -/
def pullbackAlong (N : NisnevichNeighborhood Y (f.left x)) : NisnevichNeighborhood X x :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk (pullback.snd N.toBase.left f.left))
    (Over.homMk (pullbackAlongPoint f x N) (pullback.lift_snd _ _ _)),
    by
      change smoothSeparatedFiniteType (pullback.snd N.toBase.left f.left ≫ X.hom)
      exact (etalePullback N.toBase f).prop⟩

/-- The literal projection from the source neighborhood to the target neighborhood. -/
def pullbackAlongToTarget (N : NisnevichNeighborhood Y (f.left x)) :
    (nisnevichNeighborhoodFunctor X x).obj (pullbackAlong f x N) ⟶
      (nisnevichNeighborhoodFunctor Y (f.left x)).obj N :=
  homMk (pullback.fst N.toBase.left f.left) (by
    change pullback.fst N.toBase.left f.left ≫ (N.toBase.left ≫ Y.hom) =
      pullback.snd N.toBase.left f.left ≫ X.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, MorphismProperty.Over.w])

@[reassoc]
theorem pullbackAlongToTarget_toBase (N : NisnevichNeighborhood Y (f.left x)) :
    pullbackAlongToTarget f x N ≫ N.toBase = (pullbackAlong f x N).toBase ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

@[simp]
theorem pullbackAlongToTarget_center (N : NisnevichNeighborhood Y (f.left x)) :
    (pullbackAlongToTarget f x N).left (pullbackAlong f x N).center = N.center := by
  have h := congrArg (fun g : Spec (X.left.residueField x) ⟶ N.obj.obj.left => g default)
    (pullback.lift_fst (pullbackAlongTargetPoint f x N)
      (X.left.fromSpecResidueField x) (pullbackAlongTargetPoint_toBase f x N))
  change (pullbackAlongToTarget f x N).left (pullbackAlong f x N).center =
    N.obj.val.left (Spec.map (f.left.residueFieldMap x) default) at h
  have he : Spec.map (f.left.residueFieldMap x) default =
      (default : Spec (Y.left.residueField (f.left x))) := Subsingleton.elim _ _
  exact h.trans (congrArg N.obj.val.left he)

/-- Refinement of actual target neighborhoods induces an actual source refinement. -/
def pullbackAlongMap {N M : NisnevichNeighborhood Y (f.left x)} (q : N ⟶ M) :
    pullbackAlong f x N ⟶ pullbackAlong f x M := by
  let p : pullback N.toBase.left f.left ⟶ pullback M.toBase.left f.left :=
    pullback.lift (pullback.fst N.toBase.left f.left ≫ q.hom.hom.left)
      (pullback.snd N.toBase.left f.left) (by
        rw [Category.assoc]
        have hq : q.hom.hom.left ≫ M.toBase.left = N.toBase.left :=
          MorphismProperty.Over.w q.hom.hom
        rw [hq, pullback.condition])
  refine ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk p (pullback.lift_snd _ _ _)) ?_)
  apply Over.OverMorphism.ext
  change pullbackAlongPoint f x N ≫ p = pullbackAlongPoint f x M
  apply pullback.hom_ext
  · simp only [Category.assoc, p, pullback.lift_fst]
    rw [← Category.assoc, pullbackAlongPoint, pullback.lift_fst,
      pullbackAlongPoint, pullback.lift_fst]
    dsimp only [pullbackAlongTargetPoint]
    rw [Category.assoc, refinement_point]
  · simp only [Category.assoc, p, pullback.lift_snd, pullbackAlongPoint]

@[reassoc]
theorem pullbackAlongMap_toTarget {N M : NisnevichNeighborhood Y (f.left x)}
    (q : N ⟶ M) :
    (nisnevichNeighborhoodFunctor X x).map (pullbackAlongMap f x q) ≫
        pullbackAlongToTarget f x M =
      pullbackAlongToTarget f x N ≫ (nisnevichNeighborhoodFunctor Y (f.left x)).map q := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

end Motivic.SmoothSite.NisnevichNeighborhood

namespace Motivic.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {X Y : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (f : X ⟶ Y) (x : X.left)
open NisnevichNeighborhood

/-- Restrict every original target representative on its actual pointed pullback. -/
def originalGermPullbackCocone :
    Cocone ((nisnevichNeighborhoodFunctor Y (f.left x)).op ⋙ F) where
  pt := (nisnevichPointFiberCocone X x F).pt
  ι :=
    { app := fun N => F.map (pullbackAlongToTarget f x N.unop).op ≫
        (nisnevichPointFiberCocone X x F).ι.app (op (pullbackAlong f x N.unop))
      naturality := by
        intro N M q
        change F.map ((nisnevichNeighborhoodFunctor Y (f.left x)).map q.unop).op ≫
            (F.map (pullbackAlongToTarget f x M.unop).op ≫
              (nisnevichPointFiberCocone X x F).ι.app (op (pullbackAlong f x M.unop))) =
          (F.map (pullbackAlongToTarget f x N.unop).op ≫
            (nisnevichPointFiberCocone X x F).ι.app (op (pullbackAlong f x N.unop))) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← F.map_comp, ← op_comp,
          ← pullbackAlongMap_toTarget, op_comp, F.map_comp, Category.assoc]
        have h := (nisnevichPointFiberCocone X x F).w (pullbackAlongMap f x q.unop).op
        exact congrArg (fun t => F.map (pullbackAlongToTarget f x N.unop).op ≫ t) h }

/-- Pullback of original Nisnevich germs, induced by the existing fiber colimit.
No transfer, sheaf, or compatibility law is used in this construction. -/
def originalGermPullback : (nisnevichPointFiberCocone Y (f.left x) F).pt ⟶
    (nisnevichPointFiberCocone X x F).pt :=
  (isColimitNisnevichPointFiberCocone Y (f.left x) F).desc (originalGermPullbackCocone F f x)

@[reassoc]
theorem originalGermPullback_ι (N : NisnevichNeighborhood Y (f.left x)) :
    (nisnevichPointFiberCocone Y (f.left x) F).ι.app (op N) ≫ originalGermPullback F f x =
      F.map (pullbackAlongToTarget f x N).op ≫
        (nisnevichPointFiberCocone X x F).ι.app (op (pullbackAlong f x N)) :=
  (isColimitNisnevichPointFiberCocone Y (f.left x) F).fac (originalGermPullbackCocone F f x) _

/-- The colimit-induced germ pullback agrees with actual restriction on sections. -/
@[reassoc]
theorem sectionToNisnevichPoint_originalGermPullback :
    sectionToNisnevichPoint F Y (f.left x) ≫ originalGermPullback F f x =
      F.map f.op ≫ sectionToNisnevichPoint F X x := by
  rw [sectionToNisnevichPoint, Category.assoc, originalGermPullback_ι,
    ← Category.assoc, ← F.map_comp, ← op_comp, pullbackAlongToTarget_toBase,
    op_comp, F.map_comp, Category.assoc, restriction_sectionToNisnevichPoint]

end Motivic.SmoothSite

namespace Motivic.FiniteCorrespondenceGenerator
local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsNoetherian T.left)
local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
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
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
open SmoothSite.NisnevichNeighborhood

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
    rw [hz, pullbackAlongToTarget_center] at h
    exact h.symm
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
