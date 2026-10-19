/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.MilnorEquivalenceNaturality
public import Lean.Util.CollectAxioms

/-! Direct original derived transfer and field-map consumers in all weights. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open DiagonalMilnorBoundaryDescent DiagonalMilnorEquivalenceNaturality
universe w u
namespace MotivicTest.DiagonalMilnorEquivalenceNaturality
variable {k L : Type u} [Field k] [CharZero k] [Field L] [CharZero L]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- Naturality on an arbitrary original derived class, not just a Milnor symbol. -/
theorem actual_inverse_naturality (φ : k →+* L) (q : ℕ)
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicNorm L q (motivicCohomologyFieldChange φ q q x) =
      MilnorK.map q φ (motivicNorm k q x) := motivicNorm_fieldChange φ q x

/-- Finite pushforward on every derived class becomes the already constructed Milnor norm. -/
theorem actual_inverse_transfer [Algebra k L] [Module.Finite k L] (q : ℕ)
    (x : motivicCohomology L q q (SmoothSite.base (Spec (.of L)))) :
    motivicNorm k q (DiagonalCorestriction.motivicCorestriction (k := k) (E := L) q x) =
      MilnorK.finiteExtensionNorm k L q (motivicNorm L q x) := motivicNorm_corestriction q x

open Lean in
run_cmd do
  for name in #[``actual_inverse_naturality, ``actual_inverse_transfer,
      ``rawNorm_fieldChange, ``rawNorm_corestriction,
      ``motivicSymbol_finiteExtensionNorm] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual diagonal equivalence field-map and transfer squares: standard foundations only."

end MotivicTest.DiagonalMilnorEquivalenceNaturality
