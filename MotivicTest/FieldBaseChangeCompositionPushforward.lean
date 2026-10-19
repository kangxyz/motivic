/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.CompositionPushforward

/-!
# Actual whole-incidence field-change pushforward consumers

All coefficients are arbitrary integers. Every original incidence degree and
every branch length survives in an equality of complete actual integral cycles.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.FieldBaseChangeCompositionPushforward
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The whole actual signed assembly agrees with pushforward after arbitrary field change. -/
theorem allSignedWeights (c : genericPoints (A.incidence B) → ℤ) :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceMap φ B)
      (IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeIncidence φ B)
        (fun w => c (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
          A.fieldBaseChangeIncidenceFiberMultiplicity φ B w)) =
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Z) φ
        (A.incidenceCycleAssembly k B c)) :=
  A.finitePushforward_fieldBaseChangeIncidenceCycle φ B c

/-- The original actual Tor coefficients supply the composition specialization. -/
theorem actualTorWeights :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceMap φ B)
      (IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeIncidence φ B)
        (fun w => A.incidenceTorCoefficient (S := Spec (.of k)) B
            (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
          A.fieldBaseChangeIncidenceFiberMultiplicity φ B w)) =
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Z) φ
        (A.incidenceTorCorrespondence k B)) :=
  A.finitePushforward_fieldBaseChangeIncidenceTorCycle φ B

open Lean in
run_cmd do
  for name in #[``allSignedWeights, ``actualTorWeights,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidenceComponentImageMap_ambient,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidenceComponent_pushforward,
      ``FiniteCorrespondenceGenerator.toIntegralCycle_fieldBaseChangeIncidenceImage] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual whole-incidence field-change pushforward uses only standard foundations."

end MotivicTest.FieldBaseChangeCompositionPushforward
