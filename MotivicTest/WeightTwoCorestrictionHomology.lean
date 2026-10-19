/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionHomology
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual corestriction on original weight-two homology

The genuine endpoint proof is consumed to obtain a map on the original raw
homology group. No boundary preservation hypothesis or replacement group is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic
open WeightTwoCorestriction
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open WeightOnePointNorm
open WeightOneBoundaryNorm

universe u

namespace MotivicTest.WeightTwoCorestrictionHomology

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The transferred raw representative has the exact transferred signed point class. -/
theorem actual_raw_representative (α : point E ⟶ WeightTwoSymbols.target E) :
    WeightTwoSymbols.rawClass k
      (rawDegreeTwoPushforward (k := k) (E := E)
        ((motivicRawBaseComplexXIso E 2 0).inv
          ((toReducedTorus E 2).hom.app (op (Cor.simplexProduct (point E) 0))
            (ULift.up ((zeroProductIso E).hom ≫ α))))) =
      WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α) :=
  rawDegreeTwoPushforward_cycleClass α

omit [Field E] [Algebra k E] [Module.Finite k E] in
/-- The target remains the original raw homology group, with actual cycle representatives. -/
theorem actual_cycle_representatives (x : (motivicRawBaseComplex k 2).homology 2) :
    ∃ α : point k ⟶ WeightTwoSymbols.target k, WeightTwoSymbols.cycleClass k α = x :=
  WeightTwoSymbols.cycleClass_surjective k x

/-- The actual positively shifted raw differential is preserved. -/
theorem actual_raw_boundary :
    rawDegreeOnePushforward (k := k) (E := E) ≫ (motivicRawBaseComplex k 2).d 1 2 =
      (motivicRawBaseComplex E 2).d 1 2 ≫ rawDegreeTwoPushforward (k := k) (E := E) :=
  rawPushforward_d

/-- The actual original homology transfer has the full signed finite cycle formula. -/
theorem actual_homology_class (α : point E ⟶ WeightTwoSymbols.target E) :
    corestriction (k := k) (WeightTwoSymbols.cycleClass E α) =
      WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α) :=
  corestriction_cycleClass α

/-- Signed classes retain their integer multiplicities in the original target group. -/
theorem actual_signed_class (n : ℤ) (α : point E ⟶ WeightTwoSymbols.target E) :
    corestriction (k := k) (n • WeightTwoSymbols.cycleClass E α) =
      n • WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α) := by
  rw [map_zsmul, corestriction_cycleClass]

open Lean in
run_cmd do
  for name in #[``WeightTwoSymbols.rawClass_surjective, ``WeightTwoSymbols.cycleClass_surjective,
      ``rawDegreeOnePushforward, ``rawDegreeTwoPushforward, ``pointPushforward,
      ``rawDegreeTwoPushforward_cycleClass, ``actual_raw_representative,
      ``actual_cycle_representatives, ``reducedPushforward_face, ``reducedPushforward_d,
      ``rawPushforward_d, ``rawPushforward_boundary, ``corestrictionHom, ``corestriction,
      ``corestriction_class, ``corestriction_rawClass, ``corestriction_cycleClass,
      ``corestriction_unique, ``motivicCorestriction, ``motivicCorestriction_comparison,
      ``actual_raw_boundary, ``actual_homology_class, ``actual_signed_class] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual original-H22 corestriction uses only standard foundations."

end MotivicTest.WeightTwoCorestrictionHomology
