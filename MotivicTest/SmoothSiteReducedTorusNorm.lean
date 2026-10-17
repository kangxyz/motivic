/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteReducedTorusNorm
public import Lean.Util.CollectAxioms

/-! # Direct audit of the original ordinary reduced norm and its singular sheaf map -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.SmoothSiteTorusDivisor Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.SmoothSiteReducedTorusNorm

variable (k : Type u) [Field k]

def actual_reduced_norm : (toPresheaf k).obj (reducedTorus k 1) ⟶
    SmoothSite.largeUnitsPresheaf (Spec (.of k)) := reducedNorm

def actual_reduced_norm_chain_map :
    SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (AlgebraicSimplex.cosimplicialSmoothSite k)
        ((toPresheaf k).obj (reducedTorus k 1)) ⟶
      SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (AlgebraicSimplex.cosimplicialSmoothSite k)
        (SmoothSite.largeUnitsPresheaf (Spec (.of k))) := reducedNormSheafMap

open Lean in
run_cmd do
  for name in #[``norm_relation_app, ``reducedNormApp, ``toReduced_reducedNormApp,
      ``reducedNorm, ``toReduced_reducedNorm, ``reducedNorm_affine_apply,
      ``reducedNormSheafMap, ``reducedNormSheafMap_f,
      ``actual_reduced_norm, ``actual_reduced_norm_chain_map] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original reduced norm and singular sheaf map use only standard Lean foundations."

end MotivicTest.SmoothSiteReducedTorusNorm
