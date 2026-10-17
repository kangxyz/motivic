/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichFamilyGeneratorLift
public import Lean.Util.CollectAxioms

/-!
# Actual finite-partition correspondence lifting consumers

The source and target arrows need not be étale. The labeled target family
has unrestricted cardinality. Empty support and repeated labels are included.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u v

namespace MotivicTest.NisnevichFamilyGeneratorLift

variable {k : Type u} [Field k] {X Y U : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom) (g : U ⟶ X)

/-- The actual Cor identity retains arbitrary labels and all original weights. -/
theorem family_factorization {I : Type v} (V : I → SmoothSite (Spec (.of k)))
    (q : ∀ i, V i ⟶ Y) (n : ℕ)
    (F : Fin n → (pullback A.projection g.left).Opens)
    (hFclosed : ∀ j, IsClosed (F j : Set (pullback A.projection g.left : Scheme)))
    (hFtop : (⨆ j, F j) = ⊤) (label : Fin n → I)
    (b : ∀ j, (F j).toScheme ⟶ (V (label j)).left)
    (hb : ∀ j, b j ≫ (q (label j)).left =
      (F j).ι ≫ pullback.fst A.projection g.left ≫ A.targetProjection) :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ A.cycle :=
  A.exists_graph_family_factorization_of_support_lift k g V q n F hFclosed hFtop label b hb

/-- Empty actual support has zero restriction, without choosing any target. -/
theorem empty_support [IsEmpty (pullback A.projection g.left : Scheme)] :
    (Cor.graphFunctor k).map g ≫ A.cycle = 0 := by
  let V : Empty → SmoothSite (Spec (.of k)) := fun i ↦ nomatch i
  let q : ∀ i, V i ⟶ Y := fun i ↦ nomatch i
  let F : Fin 0 → (pullback A.projection g.left).Opens := Fin.elim0
  have htop : (⨆ j, F j) = ⊤ := by ext z; exact isEmptyElim z
  obtain ⟨β, hβ⟩ := A.exists_graph_family_factorization_of_support_lift k g V q 0 F
    (fun j ↦ Fin.elim0 j) htop Fin.elim0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)
  simpa only [Fin.sum_univ_zero] using hβ.symm

/-- Repeated labels may be gathered into one signed correspondence. -/
theorem repeated_labels {V : SmoothSite (Spec (.of k))} (q : V ⟶ Y) (n : ℕ)
    (F : Fin n → (pullback A.projection g.left).Opens)
    (hFclosed : ∀ j, IsClosed (F j : Set (pullback A.projection g.left : Scheme)))
    (hFtop : (⨆ j, F j) = ⊤) (b : ∀ j, (F j).toScheme ⟶ V.left)
    (hb : ∀ j, b j ≫ q.left =
      (F j).ι ≫ pullback.fst A.projection g.left ≫ A.targetProjection) :
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ A.cycle := by
  obtain ⟨β, hβ⟩ := A.exists_graph_family_factorization_of_support_lift k g
    (fun _ : Unit ↦ V) (fun _ ↦ q) n F hFclosed hFtop (fun _ ↦ ()) b hb
  refine ⟨∑ j, β j, ?_⟩
  rw [Preadditive.sum_comp]
  exact hβ

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondenceGenerator.exists_graph_family_factorization_of_support_lift,
      ``family_factorization, ``empty_support, ``repeated_labels] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichFamilyGeneratorLift
