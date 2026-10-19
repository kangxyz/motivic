/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.FiniteRepresentatives.FamilyAssembly
public import Lean.Util.CollectAxioms

/-! The actual finite packed correspondence retains graph images, points and transfer values. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic
universe u v
namespace MotivicTest.FiniteRepresentativeFamilyAssembly
variable (k : Type u) [Field k] {U Y : SmoothSite (Spec (.of k))}
  {n m : ℕ} (V : Fin n → SmoothSite (Spec (.of k))) (label : Fin m → Fin n)
  (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)))

/-- Packing uses the original Cor composition and literal target coproduct map. -/
theorem actual_packed_graph_image (q : ∀ i, V i ⟶ Y) :
    FiniteCorrespondence.packFiniteFamily k V label β ≫
        (Cor.graphFunctor k).map (SmoothSite.finiteCoproductDesc q) =
      ∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j)) :=
  FiniteCorrespondence.packFiniteFamily_comp_graph k V label β q

open Lean in
run_cmd do
  for name in #[``actual_packed_graph_image,
      ``FiniteCorrespondence.packFiniteFamily_target_control,
      ``PresheafWithTransfers.transfer_packFiniteFamily,
      ``FiniteCorrespondence.exists_support_point_lift_of_mem_comp_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual packed finite lift family: standard foundations only."

end MotivicTest.FiniteRepresentativeFamilyAssembly
