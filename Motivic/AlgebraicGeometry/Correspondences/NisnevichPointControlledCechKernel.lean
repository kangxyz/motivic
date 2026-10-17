/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointControlledLifting
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechLocalExactness

/-!
# Point-local Čech contraction with actual fiber-point control

Supply residue-lift points satisfying a prescribed property only over the
selected fiber of the actual common finite support. The original clopen
lifting maps glue to a controlled whole-support lift. The original Čech
contraction then retains an actual original branch point for its first target,
and a genuinely chosen lift value for its second target.

All source and target points are arbitrary. No global covering condition,
closed-point reduction, or support inference from signed equality is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondence

/-- A point-local kernel has a controlled actual Čech boundary. Every boundary
source-fiber point comes from an original branch point, and its second target
satisfies the property of the actual input residue-lift witnesses. -/
theorem exists_pointed_cech_boundary_with_point_property
    (k : Type u) [Field k] {X Y V : SmoothSite (Spec (.of k))}
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (x : X.left) (Q : V.left → Prop)
    (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso (q.left.residueFieldMap v) ∧ Q v) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x)
      (β : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (SmoothSite.etalePullback q q)),
      (Cor.graphFunctor k).map N.toBase ≫ α =
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, B.projection z = N.center →
        ∃ (A : FiniteCorrespondenceGenerator X.hom V.hom) (_hA : A ∈ α.support) (a : A.scheme),
          A.projection a = x ∧
          A.targetProjection a = (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
          Q ((SmoothSite.etalePullbackSnd q q).left (B.targetProjection z)) := by
  let p : C ⟶ X.left := j ≫ pullback.fst X.hom Y.hom
  let target : C ⟶ Y.left := j ≫ pullback.snd X.hom Y.hom
  let l : pullback target q.left ⟶ C := pullback.fst target q.left
  have : Etale l := by dsimp [l]; infer_instance
  have : IsSeparated l := by dsimp [l]; infer_instance
  have hl : ∀ z : C, p z = x → ∃ w : (pullback target q.left : Scheme),
      l w = z ∧ IsIso (l.residueFieldMap w) ∧ Q (pullback.snd target q.left w) := by
    intro z hz
    obtain ⟨v, hv, hres, hQ⟩ := hq z hz
    have := hres
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := target) (g := q.left) z v hv.symm
    refine ⟨w, hw₁, ?_, hw₂.symm ▸ hQ⟩
    exact target.isIso_residueFieldMap_pullback_fst q.left v w hw₂
  obtain ⟨N, b₀, hb₀, hpoint⟩ :=
    SmoothSite.NisnevichNeighborhood.exists_lift_of_isFinite_with_point_property
      p l (fun w ↦ Q (pullback.snd target q.left w)) hl
  let b : pullback p N.toBase.left ⟶ V.left := b₀ ≫ pullback.snd target q.left
  have hb : b ≫ q.left = pullback.fst p N.toBase.left ≫ target := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
  obtain ⟨β, hβ, hpoints⟩ := exists_cech_boundary_of_common_support_lift_with_point_lift
    k α q hzero C j r hr N.toBase b hb
  refine ⟨N, β, hβ, ?_⟩
  intro B hB z hz
  obtain ⟨A, hA, a, d, has, hat, _, hds, hdt⟩ := hpoints B hB z
  refine ⟨A, hA, a, ?_, hat, ?_⟩
  · rw [hz, N.toBase_center] at has
    exact has
  · rw [← hdt]
    exact hpoint d (hds.trans hz)

end Motivic.FiniteCorrespondence
