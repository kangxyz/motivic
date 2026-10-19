/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Tuples.Transfers
public import Lean.Util.CollectAxioms

/-! Actual signed composition, graph restriction and identity on original Nis germs. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory
open Opposite
open AlgebraicGeometry
open Motivic
open _root_.Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.OriginalGermTupleTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y Z : SmoothSite (Spec (.of k))}

/-- Direct original correspondence composition consumer. -/
theorem actual_signed_composition (α : Cor.mk X ⟶ Cor.mk Y)
    (β : Cor.mk Y ⟶ Cor.mk Z) (x : X.left)
    (a : ∀ z : Z.left, (SmoothSite.nisnevichPointFiberCocone Z z ((toPresheaf k).obj P)).pt) :
    correspondenceGermHom k P hP x (α ≫ β) a =
      correspondenceGermHom k P hP x α (fun y => correspondenceGermHom k P hP y β a) :=
  correspondenceGermHom_comp k P hP α β x a

/-- The group at an object is the product of the original point-fiber groups. -/
theorem actual_tuple_group (X : Cor k) :
    (originalGermTuplePresheaf k P hP).sections X = AddCommGrpCat.of
      (∀ x : X.toSmoothSite.left,
        (SmoothSite.nisnevichPointFiberCocone X.toSmoothSite x ((toPresheaf k).obj P)).pt) := rfl

open Lean in
run_cmd do
  for name in #[``actual_signed_composition, ``actual_tuple_group,
      ``exists_signed_pointedGermLiftWitness, ``correspondenceGermHom_eq_of_witness,
      ``exists_composed_generator_germ_witnesses, ``correspondenceGermHom_comp,
      ``correspondenceGermHom_graph, ``correspondenceGermHom_id,
      ``originalGermTuplePresheaf, ``toOriginalGermTuplePresheaf,
      ``originalGermTupleTransfer_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual signed original-germ tuple transfers: standard foundations only."

end MotivicTest.OriginalGermTupleTransfers
