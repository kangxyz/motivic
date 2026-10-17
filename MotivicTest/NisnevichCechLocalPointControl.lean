/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechLocalExactness
public import Lean.Util.CollectAxioms

/-! # Source-fiber control from the original common-support contraction -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

/-- Original branch targets and the actual whole-support lift control both
Čech targets at an arbitrary source point, along with the signed boundary. -/
example (k : Type u) [Field k] {X Y U V : SmoothSite (Spec (.of k))}
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (g : U ⟶ X)
    (b : pullback (j ≫ pullback.fst X.hom Y.hom) g.left ⟶ V.left)
    (hb : b ≫ q.left = pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left ≫
      j ≫ pullback.snd X.hom Y.hom)
    (u : U.left) (v₁ v₂ : V.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = g.left u →
      A.targetProjection a = v₁)
    (hsecond : ∀ d : (pullback (j ≫ pullback.fst X.hom Y.hom) g.left : Scheme),
      pullback.snd (j ≫ pullback.fst X.hom Y.hom) g.left d = u → b d = v₂) :
    ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
      (Cor.graphFunctor k).map g ≫ α =
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, B.projection z = u →
        (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) = v₁ ∧
        (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) = v₂ := by
  obtain ⟨β, hβ, hpoints⟩ :=
    FiniteCorrespondence.exists_cech_boundary_of_common_support_lift_with_point_lift
      k α q hzero C j r hr g b hb
  refine ⟨β, hβ, ?_⟩
  intro B hB z hz
  obtain ⟨A, hA, a, d, has, hat, _, hds, hdt⟩ := hpoints B hB z
  exact ⟨hat.symm.trans (hfirst A hA a (has.trans (congrArg g.left hz))),
    hdt.symm.trans (hsecond d (hds.trans hz))⟩

open Lean Motivic.FiniteCorrespondenceGenerator Motivic.FiniteCorrespondence in
run_cmd do
  for name in #[``exists_cech_incidence_pairing_over_common_support_with_point_lift,
      ``exists_cech_boundary_of_finite_presentation_with_point_property,
      ``exists_cech_boundary_of_common_support_lift_with_point_lift] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual original-branch and common-support points control both Čech targets."
