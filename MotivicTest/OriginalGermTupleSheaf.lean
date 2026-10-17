/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermTupleSheaf
public import Motivic.Transfers.OriginalGermTupleEmbedding
public import Lean.Util.CollectAxioms

/-! Direct ordinary Nisnevich sheafness of the actual signed germ-tuple presheaf. -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Motivic Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.OriginalGermTupleSheaf
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))

/-- No substitute topology or replacement stalks enter the sheaf conclusion. -/
theorem actual_original_germ_tuple_sheaf :
    Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj (originalGermTuplePresheaf k P hP)) :=
  originalGermTuplePresheaf_isSheaf k P hP

open Lean in
run_cmd do
  for name in #[``actual_original_germ_tuple_sheaf,
      ``originalGermTuple_cover_injective, ``exists_originalGermTuple_local_value,
      ``existsUnique_originalGermTuple_amalgamation, ``originalGermTuplePresheaf_isSheaf,
      ``toOriginalGermTuplePresheaf_injective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual ordinary Nisnevich germ-tuple sheaf: standard foundations only."

end MotivicTest.OriginalGermTupleSheaf
