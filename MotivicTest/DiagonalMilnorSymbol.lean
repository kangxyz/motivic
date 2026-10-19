/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.MilnorSymbol
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual all-weight forward Milnor symbol

The domain is the standard symbol presentation, the codomain is the original
derived diagonal motivic group, and weights one and two retain their proved
old maps. No converse or arbitrary boundary norm is imported as an assumption.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalCycleSymbols Motivic.DiagonalMilnorSymbol

universe w u

namespace MotivicTest.DiagonalMilnorSymbol

variable (k : Type u) [Field k] [CharZero k]

/-- Every standard generator maps to its actual rational graph. -/
theorem actual_raw_symbol (n : ℕ) (a : Fin n → kˣ) :
    rawSymbol k n (MilnorK.symbol a) = graphSymbol k n a := rawSymbol_symbol k n a

/-- The old weight-one answer is retained after the standard K₁ identification. -/
theorem actual_one_compatibility (x : MilnorK.K k 1) :
    WeightOneHomologyNorm.homologyNorm k (rawSymbol k 1 x) = MilnorK.oneEquiv k x :=
  rawSymbol_one_comparison k x

/-- The old K₂ symbol is retained through the explicit standard comparison. -/
theorem actual_two_compatibility (x : MilnorK.K k 2) :
    rawSymbol k 2 x = WeightTwoMilnorSymbol.rawMilnorSymbol k (MilnorK.twoEquiv k x) :=
  rawSymbol_two_comparison k x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The forward map targets precisely the original derived cohomology. -/
def actual_derived_symbol (n : ℕ) : MilnorK.K k n →+
    motivicCohomology k n n (SmoothSite.base (Spec (.of k))) := motivicSymbol k n

/-- The literal graph representative is fixed by the original comparison. -/
theorem actual_derived_generator (n : ℕ) (a : Fin n → kˣ) :
    actual_derived_symbol k n (MilnorK.symbol a) =
      (motivicRawBaseEvaluationComparison k n n).symm (graphSymbol k n a) :=
  motivicSymbol_symbol k n a

open Lean in
run_cmd do
  for name in #[``graphSymbol_isSymbolMap, ``rawSymbol, ``rawSymbol_symbol,
      ``graphSymbol_one_weight, ``rawSymbol_one_comparison, ``graphSymbol_two_weight,
      ``rawSymbol_two_comparison, ``motivicSymbol, ``motivicSymbol_comparison,
      ``motivicSymbol_symbol, ``motivicSymbol_two_comparison, ``actual_raw_symbol,
      ``actual_one_compatibility, ``actual_two_compatibility, ``actual_derived_symbol,
      ``actual_derived_generator] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight Milnor-to-motivic symbol uses only standard foundations."

end MotivicTest.DiagonalMilnorSymbol
