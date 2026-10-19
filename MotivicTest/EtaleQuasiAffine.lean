/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.QuasiAffine

/-! # Original affine-line étale source consumer -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Motivic.MotivicTest.EtaleQuasiAffine

universe u
/-- No affine source or compactification is supplied to obtain quasi-affineness. -/
theorem original_source_quasiAffine {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p] :
    Y.IsQuasiAffine :=
  Scheme.isQuasiAffine_of_etale_affine_target p

open Lean in
run_cmd do
  for name in #[``Scheme.isQuasiAffine_of_etale_affine_target, ``original_source_quasiAffine] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original étale-source quasi-affineness uses only standard foundations."

end Motivic.MotivicTest.EtaleQuasiAffine
