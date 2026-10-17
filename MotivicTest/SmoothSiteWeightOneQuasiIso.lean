module

import Motivic.AlgebraicGeometry.SmoothSiteWeightOneQuasiIso
import Lean.Util.CollectAxioms

/-! # The actual reduced norm quasi-isomorphism and its foundations -/

universe u

example (k : Type u) [Field k] :
    QuasiIso (Motivic.SmoothSiteTorusDivisor.reducedNormSheafMap (k := k)) :=
  inferInstance

open Lean in
run_cmd do
  for dependency in ← collectAxioms ``Motivic.reducedNormSheafMap_quasiIso do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "Actual reduced norm depends on unsupported assumption {dependency}"
  logInfo "Actual reduced norm quasi-isomorphism uses only standard foundations."
