/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.ChosenLifting
public import Motivic.Aglib.AlgebraicGeometry.ResidueField.ResidueFieldLiftIsomorphism
public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Families.GeneratorLift

/-!
# Branch-controlled correspondence lifts at arbitrary scheme points

Retain the actual chosen residue-lift value on each clopen finite-support
piece. Surjectivity of the original finite component map onto its scheme image
then carries that value to each surviving generator's source fiber. This
produces designated-center control at arbitrary source and target points,
including target centers which specialize to each other.

No removal of other target centers, closed-point conservativity, or altered
Cor composition is used. Independence of different lift choices and the full
all-point acyclic transfer envelope remain separate constructions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

/-- Exact input residue-lift points become the only target centers of the
constructed signed branches over the distinguished source point. -/
theorem exists_pointed_graph_family_factorization_at_chosen_points
    (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left] (chosen : ∀ i, (V i).left)
    (hq : ∀ a : A.scheme, A.projection a = x →
      ∃ i : I, (q i).left (chosen i) = A.targetProjection a ∧
        IsIso ((q i).left.residueFieldMap (chosen i))) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x) (n : ℕ) (label : Fin n → I)
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support →
        (∃ r : B.scheme ⟶ pullback A.projection N.toBase.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom
            ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom N.toBase.left
            (MorphismProperty.Over.w N.toBase) A.inclusion =
          B.graphPostcompositionMap (q (label j)).left
            (MorphismProperty.Over.w (q (label j)))) ∧
        ∀ z : B.scheme, B.projection z = N.center → B.targetProjection z = chosen (label j) := by
  let W (i : I) : Scheme := pullback A.targetProjection (q i).left
  let r (i : I) : W i ⟶ A.scheme := pullback.fst A.targetProjection (q i).left
  let Q (i : I) (w : W i) : Prop :=
    pullback.snd A.targetProjection (q i).left w = chosen i
  have : ∀ i, Etale (r i) := by intro i; dsimp [r, W]; infer_instance
  have : ∀ i, IsSeparated (r i) := by intro i; dsimp [r, W]; infer_instance
  have hr : ∀ a : A.scheme, A.projection a = x →
      ∃ (i : I) (w : W i), r i w = a ∧ IsIso ((r i).residueFieldMap w) ∧ Q i w := by
    intro a ha
    obtain ⟨i, hi, hres⟩ := hq a ha
    have := hres
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := A.targetProjection) (g := (q i).left) a (chosen i) hi.symm
    refine ⟨i, w, hw₁, ?_, hw₂⟩
    exact A.targetProjection.isIso_residueFieldMap_pullback_fst (q i).left (chosen i) w hw₂
  obtain ⟨N, n, F, hF, _, htop, label, b₀, hb₀⟩ :=
    SmoothSite.NisnevichNeighborhood.exists_family_lift_of_isFinite_with_point_property
      A.projection W r Q hr
  let b (j : Fin n) : (F j).toScheme ⟶ (V (label j)).left :=
    b₀ j ≫ pullback.snd A.targetProjection (q (label j)).left
  have hb (j : Fin n) : b j ≫ (q (label j)).left =
      (F j).ι ≫ pullback.fst A.projection N.toBase.left ≫ A.targetProjection := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, (hb₀ j).1]
    simp only [Category.assoc]
  obtain ⟨β, hβ, hrβ⟩ := A.exists_graph_family_factorization_with_fiber_lift
    k N.toBase V q n F (fun j ↦ (hF j).1.1) htop label b hb
  refine ⟨N, n, label, β, hβ, ?_⟩
  intro j B hB
  refine ⟨(hrβ j B hB).1, ?_⟩
  intro z hz
  obtain ⟨t, hts, htt⟩ := (hrβ j B hB).2 z
  obtain ⟨w, hw, hval⟩ := (hb₀ j).2
  have hbt : b j t = chosen (label j) := by
    change pullback.snd A.targetProjection (q (label j)).left (b₀ j t) = chosen (label j)
    rw [hval t (hts.trans hz)]
    exact hw
  exact htt.symm.trans hbt

/-- Arbitrary chosen neighborhood representatives over all relevant target
points admit a finite branch-controlled lift. The selected set need not be
closed or have mutually incomparable points. -/
theorem exists_pointed_germ_family_factorization
    (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (T : Set Y.left)
    (hAT : ∀ a : A.scheme, A.projection a = x → A.targetProjection a ∈ T)
    (R : ∀ y : T, SmoothSite.NisnevichNeighborhood Y y.val) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x) (n : ℕ) (label : Fin n → T)
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (label j).val).obj (R (label j)))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (R (label j)).toBase) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support → ∀ z : B.scheme, B.projection z = N.center →
        B.targetProjection z = (R (label j)).center := by
  let V (y : T) := (SmoothSite.nisnevichNeighborhoodFunctor Y y.val).obj (R y)
  let q (y : T) : V y ⟶ Y := (R y).toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp [q]; infer_instance
  have hq : ∀ a : A.scheme, A.projection a = x →
      ∃ y : T, (q y).left (R y).center = A.targetProjection a ∧
        IsIso ((q y).left.residueFieldMap (R y).center) := by
    intro a ha
    let y : T := ⟨A.targetProjection a, hAT a ha⟩
    refine ⟨y, (R y).toBase_center, ?_⟩
    exact (R y).toBase.left.isIso_residueFieldMap_of_canonicalPoint_lift
      y.val (R y).obj.val.left (Over.w (R y).obj.val)
  obtain ⟨N, n, label, β, hβ, hrβ⟩ := A.exists_pointed_graph_family_factorization_at_chosen_points
    k x V q (fun y ↦ (R y).center) hq
  exact ⟨N, n, label, β, hβ, fun j B hB ↦ (hrβ j B hB).2⟩

end Motivic.FiniteCorrespondenceGenerator
