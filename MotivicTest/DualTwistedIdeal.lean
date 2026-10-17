/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdeal

/-! # Literal line-bundle domains for the product-section construction -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace Motivic.MotivicTest.DualTwistedIdeal
universe u

example (X : Scheme.{u}) (I T S : LineBundle X) :
    tensorSheaf X I.val
      (tensorSheaf X (dualLineBundle X T).val (dualLineBundle X S).val) ≅
    tensorSheaf X (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val
      (dualLineBundle X S).val := dualTwistedIdealProductIso X I T S

open Lean in
run_cmd do
  for name in #[``twistedIdealPairingIso, ``dualTwistedIdealIso,
      ``dualTwistedIdealProductIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual twisted-ideal line-bundle isomorphisms use only standard foundations."

end Motivic.MotivicTest.DualTwistedIdeal
