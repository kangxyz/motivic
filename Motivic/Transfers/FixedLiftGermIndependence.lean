/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteSupportGermLocality
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointRefinement

/-!
# Independence of sections for a fixed branch-controlled correspondence lift

When the selected source fiber of a signed correspondence has just one target
center, zero at that center implies zero after transfer at the source. This
works at arbitrary scheme points: one actual zero representative suffices.

Applying this to each branch shows that the finite evaluation of a fixed
branch-controlled lift depends only on the designated target center germs.
The original point-fiber cocone and signed Cor action are retained. This does
not identify evaluations from different correspondence-lift choices and does
not assert that closed points suffice for the full acyclic envelope.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Motivic.PresheafWithTransfers

variable (k : Type u) [Field k]
  (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))}

/-- For a generator whose chosen source fiber has one target center, a zero
target germ has zero transferred source germ, with no closed-point hypothesis. -/
theorem generator_transfer_germ_eq_zero_of_single_center
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left) (y : Y.left)
    (hA : ∀ z : A.scheme, A.projection z = x → A.targetProjection z = y)
    (s : P.sections (Cor.mk Y))
    (hs : SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y y s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x
      (P.transfer A.cycle s) = 0 := by
  obtain ⟨M, hM⟩ := (SmoothSite.sectionToNisnevichPoint_eq_zero_iff.{u, v}
    ((toPresheaf k).obj P) (X := Y) (x := y) s).mp hs
  let V (_ : Unit) := (SmoothSite.nisnevichNeighborhoodFunctor Y y).obj M
  let q (i : Unit) : V i ⟶ Y := M.toBase
  have hqEt : ∀ i, Etale (q i).left := by intro i; dsimp [q]; infer_instance
  have hq : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : Unit) (v : (V i).left), (q i).left v = A.targetProjection z ∧
        IsIso ((q i).left.residueFieldMap v) := by
    intro z hz
    exact ⟨(), M.center, M.toBase_center.trans (hA z hz).symm, inferInstance⟩
  apply (SmoothSite.sectionToNisnevichPoint_eq_zero_iff _ _).mpr
  exact @exists_restriction_transfer_eq_zero_of_family _ _ P X Y A x Unit V q
    hqEt hq s (fun _ ↦ hM)

/-- The one-center locality result extends through the actual signed finite
basis expansion, including cancellations and empty support. -/
theorem transfer_germ_eq_zero_of_single_center
    (α : FiniteCorrespondence X.hom Y.hom) (x : X.left) (y : Y.left)
    (hα : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x → A.targetProjection z = y)
    (s : P.sections (Cor.mk Y))
    (hs : SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y y s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) = 0 := by
  classical
  let ι : P.sections (Cor.mk X) ⟶
      ((SmoothSite.nisnevichPoint X x).presheafFiber (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((toPresheaf k).obj P) :=
    SmoothSite.sectionToNisnevichPoint.{u, v} ((toPresheaf k).obj P) X x
  let L : (Cor.mk X ⟶ Cor.mk Y) →+
      ((SmoothSite.nisnevichPoint X x).presheafFiber (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((toPresheaf k).obj P) :=
    { toFun := fun γ ↦ ι (P.transfer γ s)
      map_zero' := by simp
      map_add' := fun γ δ ↦ by
        simp only [transfer_add, AddCommGrpCat.hom_add_apply, map_add] }
  have hsum : ∑ A ∈ α.support, α A • A.cycle = α := by
    simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
      Finsupp.smul_single, smul_eq_mul, mul_one] using α.sum_single
  change L α = 0
  rw [← hsum, map_sum]
  apply Finset.sum_eq_zero
  intro A hA
  rw [map_zsmul]
  have hzero : L A.cycle = 0 :=
    generator_transfer_germ_eq_zero_of_single_center k P A x y (hα A hA) s hs
  rw [hzero, smul_zero]

/-- At arbitrary source and target points, a signed correspondence with a
single selected target center depends only on the section's germ there. -/
theorem transfer_germ_eq_of_single_center
    (α : FiniteCorrespondence X.hom Y.hom) (x : X.left) (y : Y.left)
    (hα : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x → A.targetProjection z = y)
    (s t : P.sections (Cor.mk Y))
    (hst : SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y y s =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y y t) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α t) := by
  have hzero := transfer_germ_eq_zero_of_single_center k P α x y hα (s - t)
    (by rw [map_sub, hst, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

/-- Evaluation using one fixed, branch-controlled finite lift is independent
of its section representatives. The map into the original source point is
exactly the existing fiber cocone injection. No source point is assumed closed. -/
theorem fixed_lift_germ_evaluation_eq
    (x : X.left) (N : SmoothSite.NisnevichNeighborhood X x) (n : ℕ)
    (V : Fin n → SmoothSite (Spec (.of k))) (y : ∀ j, (V j).left)
    (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶ Cor.mk (V j))
    (hβ : ∀ j A, A ∈ (β j).support → ∀ z : A.scheme,
      A.projection z = N.center → A.targetProjection z = y j)
    (s t : ∀ j, P.sections (Cor.mk (V j)))
    (hst : ∀ j, SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (V j) (y j) (s j) =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (V j) (y j) (t j)) :
    (SmoothSite.nisnevichPointFiberCocone X x ((toPresheaf k).obj P)).ι.app (op N)
        (∑ j, P.transfer (β j) (s j)) =
      (SmoothSite.nisnevichPointFiberCocone X x ((toPresheaf k).obj P)).ι.app (op N)
        (∑ j, P.transfer (β j) (t j)) := by
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply SmoothSite.nisnevichPointFiberCocone_eq_of_center_germ_eq
  exact transfer_germ_eq_of_single_center k P (β j) N.center (y j) (hβ j) (s j) (t j) (hst j)

end Motivic.PresheafWithTransfers
