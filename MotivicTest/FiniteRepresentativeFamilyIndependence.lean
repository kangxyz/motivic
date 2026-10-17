/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteRepresentativeFamilyIndependence
public import Lean.Util.CollectAxioms

/-!
# Independence of actual finite lift-family evaluations

Both signed families are packed into the actual finite disjoint union. Ordinary
Nisnevich sheaf gluing supplies its representative section. The common source,
support and matching germs are constructed by the previous actual comparisons.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace MotivicTest.FiniteRepresentativeFamilyIndependence
open Motivic Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))} {n : ℕ} (y : Fin n → Y.left)
  (R : ∀ i, SmoothSite.NisnevichNeighborhood Y (y i))
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
set_option quotPrecheck false in
local notation "V" => (fun i => (SmoothSite.nisnevichNeighborhoodFunctor Y (y i)).obj (R i))

include hP

/-- Finite branch-family evaluations are independent of both the source
neighborhood and the branch presentation over a fixed representative family. -/
theorem actual_family_evaluation_independence
    (x : X.left) (N M : SmoothSite.NisnevichNeighborhood X x)
    (δ : Cor.mk X ⟶ Cor.mk Y) {r r' : ℕ}
    (label : Fin r → Fin n) (label' : Fin r' → Fin n)
    (β : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
      Cor.mk (V (label j)))
    (β' : ∀ j, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj M) ⟶
      Cor.mk (V (label' j)))
    (hβ : (∑ j, β j ≫ (Cor.graphFunctor k).map (R (label j)).toBase) =
      (Cor.graphFunctor k).map N.toBase ≫ δ)
    (hβ' : (∑ j, β' j ≫ (Cor.graphFunctor k).map (R (label' j)).toBase) =
      (Cor.graphFunctor k).map M.toBase ≫ δ)
    (hcenter : ∀ j A, A ∈ (β j).support → ∀ z : A.scheme,
      A.projection z = N.center → A.targetProjection z = (R (label j)).center)
    (hcenter' : ∀ j A, A ∈ (β' j).support → ∀ z : A.scheme,
      A.projection z = M.center → A.targetProjection z = (R (label' j)).center)
    (a : ∀ z : Y.left, (SmoothSite.nisnevichPointFiberCocone Y z F).pt)
    (s : ∀ i, (F).obj (op (V i)))
    (hs : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (y i) F).ι.app (op (R i))
      (s i) = a (y i)) :
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N)
        (∑ j, P.transfer (β j) (s (label j))) =
      (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op M)
        (∑ j, P.transfer (β' j) (s (label' j))) := by
  exact family_transfer_cocone_eq k P hP y R x N M δ label label' β β' hβ hβ'
    hcenter hcenter' a s hs

open Lean in
run_cmd do
  for name in #[``actual_family_evaluation_independence,
      ``transfer_cocone_eq_of_finite_representatives_common_source,
      ``FiniteCorrespondence.packFiniteFamily_target_control] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite-family evaluations: standard foundations only."

end MotivicTest.FiniteRepresentativeFamilyIndependence
