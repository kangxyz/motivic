/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorNormRetraction
public import Lean.Util.CollectAxioms

/-! Retraction of the original all-weight Milnor symbol into genuine motivic cohomology. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalMilnorBoundaryDescent
universe w u
namespace MotivicTest.DiagonalMilnorNormRetraction
variable (k : Type u) [Field k] [CharZero k]

/-- The existing forward all-weight symbol is actually split injective. -/
theorem actual_symbol_left_inverse (q : ℕ) (x : MilnorK.K k q) :
    rawNorm k q (DiagonalMilnorSymbol.rawSymbol k q x) = x := rawNorm_rawSymbol k q x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original derived Milnor symbol is a section of the actual derived norm. -/
theorem actual_derived_symbol_left_inverse (q : ℕ) (x : MilnorK.K k q) :
    motivicNorm k q (DiagonalMilnorSymbol.motivicSymbol k q x) = x :=
  motivicNorm_motivicSymbol k q x

open Lean in
run_cmd do
  for name in #[``actual_symbol_left_inverse, ``actual_derived_symbol_left_inverse,
      ``rawNorm_rawSymbol, ``rawSymbol_injective, ``rawNorm_surjective,
      ``motivicNorm_motivicSymbol, ``motivicSymbol_injective, ``motivicNorm_surjective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original all-weight Milnor symbol retraction: standard foundations only."

end MotivicTest.DiagonalMilnorNormRetraction
