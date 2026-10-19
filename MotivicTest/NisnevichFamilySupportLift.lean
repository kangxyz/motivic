/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Families.GeneratorLift
public import Lean.Util.CollectAxioms

/-! # Consumers of actual support maps in the original signed family lift -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u v

variable (k : Type u) [Field k] {X Y U : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom) (g : U ⟶ X)
  {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
  (n : ℕ) (F : Fin n → (pullback A.projection g.left).Opens)
  (hFclosed : ∀ j, IsClosed (F j : Set (pullback A.projection g.left : Scheme)))
  (hFtop : (⨆ j, F j) = ⊤) (label : Fin n → I)
  (b : ∀ j, (F j).toScheme ⟶ (V (label j)).left)
  (hb : ∀ j, b j ≫ (q (label j)).left =
    (F j).ι ≫ pullback.fst A.projection g.left ≫ A.targetProjection)

/-- Each signed branch carries the literal source and target triangles to the
whole original support. Neither the family nor the base map must be étale. -/
example : ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
    (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
      (Cor.graphFunctor k).map g ≫ A.cycle ∧
    ∀ j B, B ∈ (β j).support → ∃ r : B.scheme ⟶ pullback A.projection g.left,
      r ≫ pullback.snd A.projection g.left = B.projection ∧
      r ≫ pullback.fst A.projection g.left ≫ A.targetProjection =
        B.targetProjection ≫ (q (label j)).left := by
  obtain ⟨β, hβ, hrβ⟩ := A.exists_graph_family_factorization_with_support_lift
    k g V q n F hFclosed hFtop label b hb
  refine ⟨β, hβ, ?_⟩
  intro j B hB
  obtain ⟨r, hr⟩ := hrβ j B hB
  refine ⟨r, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f ≫ pullback.fst U.hom Y.hom) hr
    simp only [Category.assoc, ClosedImageBaseChange.inclusion_fst,
      FiniteCorrespondenceGenerator.graphPostcompositionMap_fst] at h
    exact h
  · have h := congrArg (fun f ↦ f ≫ pullback.snd U.hom Y.hom) hr
    simp only [Category.assoc, ClosedImageBaseChange.inclusion_snd,
      FiniteCorrespondenceGenerator.graphPostcompositionMap_snd] at h
    exact h

open Lean Motivic.FiniteCorrespondenceGenerator in
run_cmd do
  for name in #[``exists_graph_family_factorization_with_support_lift,
      ``exists_graph_family_factorization_of_support_lift] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The original signed family lift retains actual whole-support maps."
