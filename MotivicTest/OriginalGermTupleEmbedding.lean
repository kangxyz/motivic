/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermTupleEmbedding
public import Lean.Util.CollectAxioms

/-! Original all-point germs detect sections without replacing the stalks. -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Motivic Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.OriginalGermTupleEmbedding
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))

/-- The genuine transfer-natural map into the original tuples is injective. -/
theorem actual_original_germ_embedding (X : Cor k) :
    Function.Injective ((toOriginalGermTuplePresheaf k P hP).hom.app (op X)) :=
  toOriginalGermTuplePresheaf_injective k P hP X

open Lean in
run_cmd do
  for name in #[``actual_original_germ_embedding,
      ``SmoothSite.section_eq_zero_of_original_germs,
      ``SmoothSite.original_germ_tuple_injective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual original-germ tuple embedding: standard foundations only."

end MotivicTest.OriginalGermTupleEmbedding
