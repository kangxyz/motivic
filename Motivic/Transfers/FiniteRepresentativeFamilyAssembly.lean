/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteRepresentativeLiftIndependence
public import Motivic.AlgebraicGeometry.Correspondences.GraphPostcompositionPointControl

/-! # Packing actual finite lift families into their literal disjoint union -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace Motivic.FiniteCorrespondence
variable (k : Type u) [Field k] {U Y : SmoothSite (Spec (.of k))}
  {n m : ℕ} (V : Fin n → SmoothSite (Spec (.of k))) (label : Fin m → Fin n)
  (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)))

/-- The original signed sum of the family followed by literal component injections. -/
def packFiniteFamily : Cor.mk U ⟶ Cor.mk (SmoothSite.finiteCoproduct V) :=
  ∑ j, β j ≫ (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι V (label j))

/-- Packing preserves the exact graph image, including signed cancellations. -/
theorem packFiniteFamily_comp_graph (q : ∀ i, V i ⟶ Y) :
    packFiniteFamily k V label β ≫
        (Cor.graphFunctor k).map (SmoothSite.finiteCoproductDesc q) =
      ∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j)) := by
  simp only [packFiniteFamily, Preadditive.sum_comp, Category.assoc,
    ← Functor.map_comp, SmoothSite.finiteCoproductι_desc]

/-- Actual designated-center control is preserved by packing, not postulated. -/
theorem packFiniteFamily_target_control (chosen : ∀ i, (V i).left) (x : U.left)
    (hβ : ∀ j A, A ∈ (β j).support → ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a = chosen (label j))
    (B : FiniteCorrespondenceGenerator U.hom (SmoothSite.finiteCoproduct V).hom)
    (hB : B ∈ (packFiniteFamily k V label β).support)
    (b : B.scheme) (hb : B.projection b = x) :
    B.targetProjection b ∈
      Set.range (fun i => (SmoothSite.finiteCoproductι V i).left (chosen i)) := by
  classical
  obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum B hB
  obtain ⟨A, hA, a, hs, ht⟩ := exists_support_point_lift_of_mem_comp_graph
    (β j) (SmoothSite.finiteCoproductι V (label j)) B hj b
  refine ⟨label j, ?_⟩
  rw [hβ j A hA a (hs.trans hb)] at ht
  exact ht

end Motivic.FiniteCorrespondence
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {U : SmoothSite (Spec (.of k))} {n m : ℕ}
  (V : Fin n → SmoothSite (Spec (.of k))) (label : Fin m → Fin n)
  (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)))

/-- Transfer evaluation on the packed lift is exactly the original finite sum
of evaluations of its component restrictions. -/
theorem transfer_packFiniteFamily
    (s : P.sections (Cor.mk (SmoothSite.finiteCoproduct V))) :
    P.transfer (FiniteCorrespondence.packFiniteFamily k V label β) s =
      ∑ j, P.transfer (β j)
        (((toPresheaf k).obj P).map (SmoothSite.finiteCoproductι V (label j)).op s) := by
  let e : (Cor.mk U ⟶ Cor.mk (SmoothSite.finiteCoproduct V)) →+
      P.sections (Cor.mk U) :=
    { toFun := fun γ => P.transfer γ s
      map_zero' := by simp
      map_add' := fun γ δ => by simp only [transfer_add, AddCommGrpCat.hom_add_apply] }
  change e (∑ j, β j ≫ (Cor.graphFunctor k).map
    (SmoothSite.finiteCoproductι V (label j))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change P.transfer (β j ≫ (Cor.graphFunctor k).map
    (SmoothSite.finiteCoproductι V (label j))) s = _
  rw [transfer_comp]
  rfl

end Motivic.PresheafWithTransfers
