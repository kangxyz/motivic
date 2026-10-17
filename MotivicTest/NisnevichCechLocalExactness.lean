/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechLocalExactness
public import Lean.Util.CollectAxioms

/-!
# Local Čech exactness for arbitrary signed correspondences

These consumers use the actual correspondence category over an arbitrary field.
Equal graph images become locally equal modulo actual Čech boundaries. Arbitrary
integer coefficients, including negative coefficients, are admitted verbatim.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u v

namespace MotivicTest.NisnevichCechLocalExactness

variable {k : Type u} [Field k] {X Y V : SmoothSite (Spec (.of k))}

example (α α' : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (heq : α ≫ (Cor.graphFunctor k).map q = α' ≫ (Cor.graphFunctor k).map q)
    (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
        (Cor.graphFunctor k).map g ≫ α - (Cor.graphFunctor k).map g ≫ α' =
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
            β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) := by
  have hzero : (α - α') ≫ (Cor.graphFunctor k).map q = 0 := by
    rw [Preadditive.sub_comp, heq, sub_self]
  simpa only [Preadditive.comp_sub] using
    FiniteCorrespondence.exists_nisnevich_cech_boundary k (α - α') q hq hzero x

example {I : Type v} [Fintype I] (n : I → ℤ) (α : I → (Cor.mk X ⟶ Cor.mk V))
    (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (hzero : (∑ i, n i • α i) ≫ (Cor.graphFunctor k).map q = 0) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
        (Cor.graphFunctor k).map g ≫ (∑ i, n i • α i) =
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
            β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) :=
  FiniteCorrespondence.exists_nisnevich_cech_boundary k (∑ i, n i • α i) q hq hzero x

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondence.exists_nisnevich_cech_boundary,
      ``FiniteCorrespondence.exists_cech_boundary_of_common_support_lift,
      ``FiniteCorrespondence.exists_cech_boundary_of_finite_presentation,
      ``FiniteCorrespondenceGenerator.exists_cech_incidence_pairing_over_common_support] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichCechLocalExactness
