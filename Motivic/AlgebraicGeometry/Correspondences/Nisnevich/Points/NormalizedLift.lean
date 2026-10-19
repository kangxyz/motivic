/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Points.GeneratorLift
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Normalization
public import Motivic.Aglib.AlgebraicGeometry.ResidueField.ResidueFieldLiftIsomorphism

/-!
# Actual branch control for normalized finite-germ representatives

For the finite selected target centers, normalize each chosen neighborhood by
an actual affine open refinement. The original signed lifting construction then
has only the designated target branch over the distinguished source point.
This follows from its literal whole-support maps, not from its Cor equality.

No target covering assumption or infinite coproduct is used. The result is
representative-level data; independence of arbitrary germ representatives and
the full envelope transfer action remain separate steps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)

/-- An actual whole-support factorization forces a lifted generator's source
fiber into the designated target branch of a normalized neighborhood. -/
theorem target_eq_center_of_support_lift
    (T : Set Y.left) (hT : ∀ a : A.scheme, A.projection a = x → A.targetProjection a ∈ T)
    (N : SmoothSite.NisnevichNeighborhood X x) {y : Y.left}
    (M : SmoothSite.NisnevichNeighborhood Y y) (hM : M.toBase.left ⁻¹' T = {M.center})
    (B : FiniteCorrespondenceGenerator
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom
      ((SmoothSite.nisnevichNeighborhoodFunctor Y y).obj M).hom)
    (r : B.scheme ⟶ pullback A.projection N.toBase.left)
    (hr : r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom
        ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom N.toBase.left
        (MorphismProperty.Over.w N.toBase) A.inclusion =
      B.graphPostcompositionMap M.toBase.left (MorphismProperty.Over.w M.toBase))
    (z : B.scheme) (hz : B.projection z = N.center) : B.targetProjection z = M.center := by
  have hr₁ : r ≫ pullback.snd A.projection N.toBase.left = B.projection := by
    have h := congrArg (fun f ↦ f ≫ pullback.fst
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom Y.hom) hr
    simp only [Category.assoc, ClosedImageBaseChange.inclusion_fst,
      graphPostcompositionMap_fst] at h
    exact h
  have hr₂ : r ≫ pullback.fst A.projection N.toBase.left ≫ A.targetProjection =
      B.targetProjection ≫ M.toBase.left := by
    have h := congrArg (fun f ↦ f ≫ pullback.snd
      ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom Y.hom) hr
    simp only [Category.assoc, ClosedImageBaseChange.inclusion_snd,
      graphPostcompositionMap_snd] at h
    exact h
  have hz' : pullback.snd A.projection N.toBase.left (r z) = N.center :=
    (congrArg (fun f : B.scheme ⟶ N.obj.obj.left ↦ f z) hr₁).trans hz
  have ha : A.projection (pullback.fst A.projection N.toBase.left (r z)) = x := by
    have h := congrArg
      (fun f : pullback A.projection N.toBase.left ⟶ X.left ↦ f (r z))
      (pullback.condition (f := A.projection) (g := N.toBase.left))
    change A.projection (pullback.fst A.projection N.toBase.left (r z)) =
      N.obj.obj.hom (pullback.snd A.projection N.toBase.left (r z)) at h
    simpa only [hz',
      show N.obj.obj.hom N.center = x from N.toBase_center] using h
  have ht : M.toBase.left (B.targetProjection z) ∈ T := by
    have h := congrArg (fun f : B.scheme ⟶ Y.left ↦ f z) hr₂
    change A.targetProjection (pullback.fst A.projection N.toBase.left (r z)) =
      M.toBase.left (B.targetProjection z) at h
    exact h ▸ hT _ ha
  have : B.targetProjection z ∈ M.toBase.left ⁻¹' T := ht
  rwa [hM, Set.mem_singleton_iff] at this

/-- Any representatives over the finite relevant closed centers admit actual
normalized refinements and a signed lift with only their designated branches
above the original source point. Empty fibers and repeated finite labels are retained. -/
theorem exists_normalized_pointed_graph_family_factorization
    (T : Set Y.left) (hT : T.Finite) (hclosed : ∀ y ∈ T, IsClosed ({y} : Set Y.left))
    (hAT : ∀ a : A.scheme, A.projection a = x → A.targetProjection a ∈ T)
    (R : ∀ y : T, SmoothSite.NisnevichNeighborhood Y y.val) :
    ∃ (M : ∀ y : T, SmoothSite.NisnevichNeighborhood Y y.val)
      (ρ : ∀ y, M y ⟶ R y) (N : SmoothSite.NisnevichNeighborhood X x)
      (n : ℕ) (label : Fin n → T)
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (M (label j)))),
      (∀ y, IsAffine (M y).obj.obj.left ∧ IsOpenImmersion (ρ y).hom.hom.left ∧
        (M y).obj.val.left ≫ (ρ y).hom.hom.left = (R y).obj.val.left ∧
        (M y).toBase.left ⁻¹' T = {(M y).center}) ∧
      (∑ j, β j ≫ (Cor.graphFunctor k).map (M (label j)).toBase) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support → ∀ z : B.scheme, B.projection z = N.center →
        B.targetProjection z = (M (label j)).center := by
  classical
  have hrep (y : T) := (R y).exists_normalized_refinement T hT hclosed y.property
  choose M ρ hM using hrep
  let V (y : T) := (SmoothSite.nisnevichNeighborhoodFunctor Y y.val).obj (M y)
  let q (y : T) : V y ⟶ Y := (M y).toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp [q]; infer_instance
  have hq : ∀ a : A.scheme, A.projection a = x →
      ∃ (y : T) (v : (V y).left), (q y).left v = A.targetProjection a ∧
        IsIso ((q y).left.residueFieldMap v) := by
    intro a ha
    let y : T := ⟨A.targetProjection a, hAT a ha⟩
    refine ⟨y, (M y).center, (M y).toBase_center, ?_⟩
    exact (M y).toBase.left.isIso_residueFieldMap_of_canonicalPoint_lift
      y.val (M y).obj.val.left (Over.w (M y).obj.val)
  obtain ⟨N, n, label, β, hβ, hrβ⟩ :=
    A.exists_pointed_graph_family_factorization_with_support k x V q hq
  refine ⟨M, ρ, N, n, label, β, hM, hβ, ?_⟩
  intro j B hB z hz
  obtain ⟨r, hr⟩ := hrβ j B hB
  exact A.target_eq_center_of_support_lift k x T hAT N (M (label j))
    (hM (label j)).2.2.2 B r hr z hz

end Motivic.FiniteCorrespondenceGenerator
