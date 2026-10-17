/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichPointGeneratorLift
public import Lean.Util.CollectAxioms

/-!
# Consumers of finite-fiber correspondence lifting

These tests retain the arbitrary family universe, the complete clopen support
partition and its actual maps, and the literal signed Cor composition. Target
lifts are required only over the chosen finite source fiber.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.SmoothSite

universe u v

section FiniteSupport

variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  {I : Type v} {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
  (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z)
  [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
  (hq : ∀ z : Z, p z = x →
    ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v))

example : ∃ (N : NisnevichNeighborhood X x) (n : ℕ)
    (F : Fin n → (pullback p N.toBase.left).Opens),
    (∀ j, IsClopen (F j : Set (pullback p N.toBase.left : Scheme)) ∧
      IsFinite ((F j).ι ≫ pullback.snd p N.toBase.left)) ∧
    Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p N.toBase.left :=
  NisnevichNeighborhood.exists_family_lift_of_isFinite p V q hq

end FiniteSupport

section Correspondence

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
  {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
  [∀ i, Etale (q i).left]
  (hq : ∀ z : A.scheme, A.projection z = x →
    ∃ (i : I) (v : (V i).left), (q i).left v = A.targetProjection z ∧
      IsIso ((q i).left.residueFieldMap v))

example : ∃ (N : NisnevichNeighborhood X x) (n : ℕ) (label : Fin n → I)
    (β : ∀ j, Cor.mk ((nisnevichNeighborhoodFunctor X x).obj N) ⟶ Cor.mk (V (label j))),
    (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
      (Cor.graphFunctor k).map N.toBase ≫ A.cycle :=
  A.exists_pointed_graph_family_factorization k x V q hq

set_option backward.isDefEq.respectTransparency false in
example (c : ℤ) : ∃ (N : NisnevichNeighborhood X x) (n : ℕ) (label : Fin n → I)
    (β : ∀ j, Cor.mk ((nisnevichNeighborhoodFunctor X x).obj N) ⟶ Cor.mk (V (label j))),
    (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
      (Cor.graphFunctor k).map N.toBase ≫ (c • A.cycle) := by
  obtain ⟨N, n, label, β, hβ⟩ := A.exists_pointed_graph_family_factorization k x V q hq
  refine ⟨N, n, label, fun j ↦ c • β j, ?_⟩
  rw [Preadditive.comp_zsmul, ← hβ, Finset.smul_sum]
  simp only [Preadditive.zsmul_comp]

end Correspondence

open Lean in
run_cmd do
  for name in #[``Motivic.SmoothSite.NisnevichNeighborhood.exists_family_lift_of_isFinite,
      ``Motivic.FiniteCorrespondenceGenerator.exists_pointed_graph_family_factorization] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite-fiber point-indexed Cor lifting uses only standard Lean foundations."
