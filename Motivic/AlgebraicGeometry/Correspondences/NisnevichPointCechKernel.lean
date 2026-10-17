/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointLifting
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechLocalExactness

/-!
# A point-local Čech kernel relation on an explicit common finite support

Only the chosen common support's finite fiber needs residue-field lifts through
the étale arrow. The original support contraction then gives a literal Čech
boundary over an actual point-fiber neighborhood. There is no global target
covering hypothesis, replacement composition, or assertion in higher degrees.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A signed relation supported on an actual common closed finite image becomes
a Čech boundary after a point-index refinement if that image's selected finite
fiber admits residue-field lifts. -/
theorem exists_pointed_cech_boundary_of_common_support_fiber
    (k : Type u) [Field k] {X Y V : SmoothSite (Spec (.of k))}
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (x : X.left)
    (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso (q.left.residueFieldMap v)) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x)
      (β : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (SmoothSite.etalePullback q q)),
      (Cor.graphFunctor k).map N.toBase ≫ α =
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) := by
  let p : C ⟶ X.left := j ≫ pullback.fst X.hom Y.hom
  let target : C ⟶ Y.left := j ≫ pullback.snd X.hom Y.hom
  let l : pullback target q.left ⟶ C := pullback.fst target q.left
  have : Etale l := by dsimp [l]; infer_instance
  have : IsSeparated l := by dsimp [l]; infer_instance
  have hl : ∀ z : C, p z = x → ∃ v : (pullback target q.left : Scheme),
      l v = z ∧ IsIso (l.residueFieldMap v) := by
    intro z hz
    obtain ⟨v, hv, hres⟩ := hq z hz
    have := hres
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := target) (g := q.left) z v hv.symm
    refine ⟨w, hw₁, ?_⟩
    exact target.isIso_residueFieldMap_pullback_fst q.left v w hw₂
  obtain ⟨N, b₀, hb₀⟩ :=
    SmoothSite.NisnevichNeighborhood.exists_lift_of_isFinite p l hl
  let b : pullback p N.obj.obj.hom ⟶ V.left := b₀ ≫ pullback.snd target q.left
  have hb : b ≫ q.left = pullback.fst p N.obj.obj.hom ≫ target := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
  obtain ⟨β, hβ⟩ := exists_cech_boundary_of_common_support_lift k α q hzero
    C j r hr N.toBase b hb
  exact ⟨N, β, hβ⟩

end Motivic.FiniteCorrespondence
