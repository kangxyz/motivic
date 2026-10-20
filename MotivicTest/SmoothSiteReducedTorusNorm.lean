/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.ReducedTorusNorm
public import Lean.Util.CollectAxioms

/-! # Direct audit of the original ordinary reduced norm and its singular sheaf map -/

@[expose] public noncomputable section

open _root_.CategoryTheory.SingularComplex (sheafObj)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.SmoothSiteTorusDivisor _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.SmoothSiteReducedTorusNorm

variable (k : Type u) [Field k]

/-- The original reduced torus norm with values in the presheaf of global units. -/
def actualReducedNorm : (toPresheaf k).obj (reducedTorus k 1) ⟶
    SmoothSite.largeUnitsPresheaf (Spec (.of k)) := reducedNorm

/-- The singular sheaf map induced by the original reduced torus norm. -/
def actualReducedNormChainMap :
    sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (cosimplicialSmoothSite k)
        ((toPresheaf k).obj (reducedTorus k 1)) ⟶
      sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (cosimplicialSmoothSite k)
        (SmoothSite.largeUnitsPresheaf (Spec (.of k))) := reducedNormSheafMap

open Lean in
run_cmd do
  for name in #[``norm_relation_app, ``reducedNormApp, ``toReduced_reducedNormApp,
      ``reducedNorm, ``toReduced_reducedNorm, ``reducedNorm_affine_apply,
      ``reducedNormSheafMap, ``reducedNormSheafMap_f,
      ``actualReducedNorm, ``actualReducedNormChainMap] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original reduced norm and singular sheaf map use only standard Lean foundations."

end MotivicTest.SmoothSiteReducedTorusNorm
