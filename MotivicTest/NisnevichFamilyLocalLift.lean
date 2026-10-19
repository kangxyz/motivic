/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Families.LocalLift
public import Lean.Util.CollectAxioms

/-!
# Signed local Nisnevich-family correspondence lifting consumers

The index type and its universe are arbitrary. These consumers cover signed
subtraction and integer multiplicities, and the zero correspondence through
an empty family without a covering or nonemptiness hypothesis.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe u v

namespace MotivicTest.NisnevichFamilyLocalLift

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
  [∀ i, Etale (q i).left]
  (hq : ∀ y : Y.left, ∃ (i : I) (v : (V i).left),
    (q i).left v = y ∧ IsIso ((q i).left.residueFieldMap v)) (x : X.left)

/-- Arbitrary signed correspondences use only a finite list of family members. -/
example (α : Cor.mk X ⟶ Cor.mk Y) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (label : Fin n → I) (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ α :=
  FiniteCorrespondence.exists_nisnevich_graph_family_factorization k α V q hq x

include hq in
/-- Negative terms and arbitrary integer multiplicities require no effectivity. -/
theorem signed_subtraction_lifts (A B : FiniteCorrespondenceGenerator X.hom Y.hom)
    (c : ℤ) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (label : Fin n → I) (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ (c • A.cycle - B.cycle) :=
  FiniteCorrespondence.exists_nisnevich_graph_family_factorization k
    (c • A.cycle - B.cycle) V q hq x

/-- Even with no target object in the family, zero has a zero-branch lift. -/
theorem empty_family_zero_lifts
    (V : Empty → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (label : Fin 0 → Empty) (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ (0 : Cor.mk X ⟶ Cor.mk Y) :=
  FiniteCorrespondence.exists_nisnevich_graph_family_factorization_zero k V q x

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondenceGenerator.exists_nisnevich_graph_family_factorization,
      ``FiniteCorrespondence.exists_nisnevich_graph_family_factorization,
      ``FiniteCorrespondence.exists_nisnevich_graph_family_factorization_zero,
      ``signed_subtraction_lifts, ``empty_family_zero_lifts] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichFamilyLocalLift
