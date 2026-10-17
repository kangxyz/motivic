/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichPointControlledCechKernel
public import Lean.Util.CollectAxioms

/-! # Actual designated-point control on both sides of a local Čech relation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

/-- Gluing retains both the literal whole-support factorization and the input
property at each selected fiber point, including when that fiber is empty. -/
example {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
    {Z V : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
    (q : V ⟶ Z) [Etale q] [IsSeparated q] (Q : V → Prop)
    (hq : ∀ z : Z, p z = x →
      ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v) ∧ Q v) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x) (b : pullback p N.toBase.left ⟶ V),
      b ≫ q = pullback.fst p N.toBase.left ∧
      ∀ t : (pullback p N.toBase.left : Scheme),
        pullback.snd p N.toBase.left t = N.center → Q (b t) :=
  SmoothSite.NisnevichNeighborhood.exists_lift_of_isFinite_with_point_property p q Q hq

/-- The designated set can contain arbitrary, mutually specializing points.
Both Čech targets lie in it and have the same image under the original q. -/
example (k : Type u) [Field k] {X Y V : SmoothSite (Spec (.of k))}
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (x : X.left) (T : Set V.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso (q.left.residueFieldMap v) ∧ v ∈ T) :
    ∃ (N : SmoothSite.NisnevichNeighborhood X x)
      (β : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (SmoothSite.etalePullback q q)),
      (Cor.graphFunctor k).map N.toBase ≫ α =
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, B.projection z = N.center →
        (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∈ T ∧
        (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) ∈ T ∧
        q.left ((SmoothSite.etalePullbackFst q q).left (B.targetProjection z)) =
          q.left ((SmoothSite.etalePullbackSnd q q).left (B.targetProjection z)) := by
  obtain ⟨N, β, hβ, hpoint⟩ :=
    FiniteCorrespondence.exists_pointed_cech_boundary_with_point_property
      k α q hzero C j r hr x (fun v ↦ v ∈ T) hq
  refine ⟨N, β, hβ, ?_⟩
  intro B hB z hz
  obtain ⟨A, hA, a, has, hat, hsecond⟩ := hpoint B hB z hz
  refine ⟨hat ▸ hfirst A hA a has, hsecond, ?_⟩
  exact congrArg (fun f : (pullback q.left q.left : Scheme) ⟶ Y.left ↦
    f (B.targetProjection z)) (pullback.condition (f := q.left) (g := q.left))

open Lean Motivic in
run_cmd do
  for name in #[``SmoothSite.NisnevichNeighborhood.exists_lift_of_isFinite_with_point_property,
      ``FiniteCorrespondence.exists_pointed_cech_boundary_with_point_property] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Chosen input fiber points control both targets of the actual signed local Čech relation."
