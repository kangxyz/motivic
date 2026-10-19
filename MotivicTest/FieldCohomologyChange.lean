/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.FieldCohomologyChange
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual field-cohomology maps

The tests use the originally defined derived groups at each field, arbitrary
field maps, and the original reduction and positive Bockstein. All natural
coefficient levels are allowed, including characteristic-dividing levels.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe w u

namespace MotivicTest.FieldCohomologyChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The source and target are the actual derived groups on their own ground fields. -/
def integralMap (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) →+
      motivicCohomology L p q (SmoothSite.base (Spec (.of L))) :=
  motivicCohomologyFieldChange φ p q

/-- Every finite coefficient level uses the same geometric field map. -/
def finiteMap (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) →+
      motivicFiniteCohomology L p q n (SmoothSite.base (Spec (.of L))) :=
  motivicFiniteCohomologyFieldChange φ p q n

/-- The actual reduction square, at an arbitrary composite or prime level. -/
theorem reduction_square (p : ℤ) (q n : ℕ)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :
    finiteMap φ p q n (motivicBaseIntegralReduction k p q n x) =
      motivicBaseIntegralReduction L p q n (integralMap φ p q x) :=
  motivicCohomologyFieldChange_integralReduction φ p q n x

/-- The original positive weight-two Bockstein is preserved by every field map. -/
theorem weightTwo_bockstein (n : ℕ)
    (x : motivicFiniteCohomology k 1 2 n (SmoothSite.base (Spec (.of k)))) :
    integralMap φ 2 2 (motivicBaseBockstein k 1 2 n x) =
      motivicBaseBockstein L 1 2 n (finiteMap φ 1 2 n x) :=
  motivicCohomologyFieldChange_bockstein φ 1 2 n x

/-- Level one is included by the literal same construction. -/
def levelOne (p : ℤ) (q : ℕ) := finiteMap φ p q 1

/-- A concrete composite level is included without an invertibility premise. -/
def levelTwelve (p : ℤ) (q : ℕ) := finiteMap φ p q 12

section CharacteristicTwo

variable {E : Type} [Field E] (ψ : ZMod 2 →+* E)
variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (ZMod 2)))) AddCommGrpCat.{1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{1})]

/-- Characteristic-dividing coefficients require no separability or finiteness premise. -/
def characteristicDividing :
    motivicFiniteCohomology (ZMod 2) 1 2 2 (SmoothSite.base (Spec (.of (ZMod 2)))) →+
      motivicFiniteCohomology E 1 2 2 (SmoothSite.base (Spec (.of E))) :=
  motivicFiniteCohomologyFieldChange ψ 1 2 2

end CharacteristicTwo

open Lean in
run_cmd do
  for name in #[``motivicBaseComplexMap, ``motivicBaseComplexMap_raw,
      ``motivicBaseFiniteConeMap, ``motivicBaseFiniteConeMap_integral,
      ``motivicBaseFiniteConeMap_bockstein, ``motivicCohomologyFieldChange,
      ``motivicCohomologyFieldChange_comparison, ``motivicCohomologyFieldChange_rawComparison,
      ``motivicFiniteCohomologyFieldChange,
      ``motivicFiniteCohomologyFieldChange_comparison,
      ``motivicCohomologyFieldChange_integralReduction, ``motivicCohomologyFieldChange_bockstein,
      ``integralMap, ``finiteMap, ``reduction_square, ``weightTwo_bockstein,
      ``levelOne, ``levelTwelve, ``characteristicDividing] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field cohomology maps and coefficient squares use only standard Lean axioms."

end MotivicTest.FieldCohomologyChange
