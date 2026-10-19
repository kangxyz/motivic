/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Tuples.Envelope
public import Lean.Util.CollectAxioms

/-! The actual all-point Nisnevich transfer envelope and its injective splitting. -/
@[expose] public noncomputable section
open CategoryTheory Motivic Motivic.SheafWithTransfers
universe u
namespace MotivicTest.OriginalGermTupleEnvelope
variable (k : Type u) [Field k]

/-- Injectivity in the original transfer-sheaf category gives a genuine retract. -/
theorem actual_transfer_injective_retract (P : SheafWithTransfers.{u + 1} k) [Injective P] :
    ∃ r : originalGermEnvelope k P ⟶ P, toOriginalGermEnvelope k P ≫ r = 𝟙 P :=
  exists_originalGermEnvelope_retraction k P

open Lean in
run_cmd do
  for name in #[``actual_transfer_injective_retract, ``originalGermEnvelope,
      ``toOriginalGermEnvelope, ``toOriginalGermEnvelope_mono] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-point transfer envelope and retract: standard foundations only."

end MotivicTest.OriginalGermTupleEnvelope
