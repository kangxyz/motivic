/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.FamilyLifting
public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Families.GeneratorLift

/-!
# Finite-fiber correspondence lifts in the actual Nisnevich-neighborhood index

Only the images of the finite support fiber over the chosen source point need
residue-field lifts through the target family. The family is not required to
cover the target scheme. The existing finite clopen support decomposition and
incidence-Tor graph factorization produce signed correspondence branches over
an actual object of the point-fiber neighborhood index. Every surviving
generator retains an actual map to the original whole support pullback.

This is a representative-level prerequisite for MVW's varying closed-point
envelope. It does not yet define the envelope action on germ classes, prove
independence of representatives, or prove compatibility with Cor composition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Residue lifts only over a generator's finite source fiber give a finite
sum of actual signed correspondence lifts in the point-neighborhood index.
The displayed composition is the original incidence-Tor composition in `Cor`. -/
theorem exists_pointed_graph_family_factorization_with_support
    (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left]
    (hq : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : I) (v : (V i).left), (q i).left v = A.targetProjection z ∧
        IsIso ((q i).left.residueFieldMap v)) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x) (n : ℕ) (label : Fin n → I)
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support →
        ∃ r : B.scheme ⟶ pullback A.projection N.toBase.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom
            ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom N.toBase.left
            (MorphismProperty.Over.w N.toBase) A.inclusion =
          B.graphPostcompositionMap (q (label j)).left
            (MorphismProperty.Over.w (q (label j))) := by
  let P (i : I) : Scheme := pullback A.targetProjection (q i).left
  let r (i : I) : P i ⟶ A.scheme := pullback.fst A.targetProjection (q i).left
  have : ∀ i, Etale (r i) := by intro i; dsimp [r, P]; infer_instance
  have : ∀ i, IsSeparated (r i) := by intro i; dsimp [r, P]; infer_instance
  have hr : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : I) (v : P i), r i v = z ∧ IsIso ((r i).residueFieldMap v) := by
    intro z hz
    obtain ⟨i, v, hv, hres⟩ := hq z hz
    have := hres
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := A.targetProjection) (g := (q i).left) z v hv.symm
    refine ⟨i, w, hw₁, ?_⟩
    exact A.targetProjection.isIso_residueFieldMap_pullback_fst (q i).left v w hw₂
  obtain ⟨N, n, F, hF, _, hFtop, label, b₀, hb₀⟩ :=
    SmoothSite.NisnevichNeighborhood.exists_family_lift_of_isFinite A.projection P r hr
  let b (j : Fin n) : (F j).toScheme ⟶ (V (label j)).left :=
    b₀ j ≫ pullback.snd A.targetProjection (q (label j)).left
  have hb (j : Fin n) : b j ≫ (q (label j)).left =
      (F j).ι ≫ pullback.fst A.projection N.obj.obj.hom ≫ A.targetProjection := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
    simp only [Category.assoc]
  obtain ⟨β, hβ, hrβ⟩ := A.exists_graph_family_factorization_with_support_lift
    k N.toBase V q n F (fun j ↦ (hF j).1.1) hFtop label b hb
  exact ⟨N, n, label, β, hβ, hrβ⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original pointed finite-sum equality follows from the same constructed
support-controlled lift. -/
theorem exists_pointed_graph_family_factorization
    (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left]
    (hq : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : I) (v : (V i).left), (q i).left v = A.targetProjection z ∧
        IsIso ((q i).left.residueFieldMap v)) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x) (n : ℕ) (label : Fin n → I)
      (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map N.toBase ≫ A.cycle := by
  obtain ⟨N, n, label, β, hβ, _⟩ := A.exists_pointed_graph_family_factorization_with_support
    k x V q hq
  exact ⟨N, n, label, β, hβ⟩

end Motivic.FiniteCorrespondenceGenerator
