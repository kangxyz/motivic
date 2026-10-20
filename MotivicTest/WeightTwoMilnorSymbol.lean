/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.MilnorSymbol
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual characteristic-zero motivic Milnor symbol

The source is the original tensor/Steinberg quotient. Targets are the actual
signed raw homology and the original derived integral and finite groups.
These consumers retain literal symbols, all coefficient levels, the exact
subgroup of multiples, and the original cohomological field-change maps.
The dependency audit rejects every nonstandard assumption.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open MilnorK.K2 Motivic.WeightTwoMilnorSymbol
open scoped TensorProduct

universe u

namespace MotivicTest.WeightTwoMilnorSymbol

variable (k : Type u) [Field k] [CharZero k]

/-- The raw map has the actual original tensor quotient as its domain. -/
theorem actual_raw_symbol (a b : kˣ) :
    (rawMilnorSymbol k
      ((steinbergSpan k).mkQ (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) :
        (motivicRawBaseComplex k 2).homology 2) = WeightTwoSymbols.graphSymbol k a b :=
  rawMilnorSymbol_symbol k a b

/-- Its source remains precisely the integer span of the original Steinberg tensors. -/
theorem actual_raw_tensor_factorization (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    rawMilnorSymbol k ((steinbergSpan k).mkQ x) = WeightTwoSymbols.tensorSymbol k x :=
  rawMilnorSymbol_tensor k x

/-- The source quotient really imposes Steinberg for the actual raw graph values. -/
theorem actual_raw_steinberg (a b : kˣ) (hab : (a : k) + (b : k) = 1) :
    rawMilnorSymbol k (symbol a b) = 0 := by
  rw [steinberg a b hab, map_zero]

/-- Use the standard derived category of Nisnevich sheaves over the base field in this test. -/
local instance instHasDerivedCategoryMotivicTest : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The integral target is the actual derived group, with the original graph convention. -/
theorem actual_derived_symbol (a b : kˣ) :
    (motivicMilnorSymbol k (symbol a b) :
        motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) =
      (motivicRawBaseEvaluationComparison k 2 2).symm
        (WeightTwoSymbols.graphSymbol k a b) :=
  motivicMilnorSymbol_symbol k a b

/-- The integral tensor lift is the previously defined actual tensor symbol. -/
theorem actual_derived_tensor_factorization :
    (motivicMilnorSymbol k).comp (steinbergSpan k).mkQ.toAddMonoidHom =
      WeightTwoSymbols.motivicTensorSymbol k := motivicMilnorSymbol_tensor_square k

/-- Every coefficient level uses the original integral reduction of a literal symbol. -/
theorem actual_finite_symbol (n : ℕ) (a b : kˣ) :
    (finiteMilnorSymbol k n (symbol a b) :
        motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) =
      motivicBaseIntegralReduction k 2 2 n
        ((motivicRawBaseEvaluationComparison k 2 2).symm
          (WeightTwoSymbols.graphSymbol k a b)) :=
  finiteMilnorSymbol_symbol k n a b

/-- Reduction commutes as an equality of the actual additive maps. -/
theorem actual_reduction_square (n : ℕ) :
    (motivicBaseIntegralReduction k 2 2 n).comp (motivicMilnorSymbol k) =
      finiteMilnorSymbol k n := finiteMilnorSymbol_reduction_square k n

omit [CharZero k] in
/-- The subgroup used in the second quotient is exactly the subgroup of multiples. -/
theorem exact_milnor_multiples (n : ℕ) (x : MilnorK.K2.Group k) :
    x ∈ milnorMultiples k n ↔ ∃ y : MilnorK.K2.Group k, n • y = x := mem_milnorMultiples k n x

/-- Quotient reduction retains the actual integral reduction without any comparison premise. -/
theorem actual_modulo_reduction_square (n : ℕ) :
    (finiteMilnorSymbolModulo k n).comp (QuotientAddGroup.mk' (milnorMultiples k n)) =
      (motivicBaseIntegralReduction k 2 2 n).comp (motivicMilnorSymbol k) :=
  finiteMilnorSymbolModulo_reduction_square k n

/-- The finite top-degree comparison retains the same actual integral symbol class. -/
theorem actual_top_degree_comparison (n : ℕ) (x : MilnorK.K2.Group k) :
    FieldTopDegree.topDegreeFiniteEquiv k 2 n
        (finiteMilnorSymbolModulo k n (QuotientAddGroup.mk x)) =
      (QuotientAddGroup.mk (motivicMilnorSymbol k x) :
        FieldTopDegree.integralModulo k 2 n) :=
  finiteMilnorSymbol_topDegree_comparison k n x

/-- Level zero is included in the actual modulo construction. -/
theorem coefficient_zero (x : MilnorK.K2.Group k) :
    finiteMilnorSymbolModulo k 0 (QuotientAddGroup.mk x) =
      motivicBaseIntegralReduction k 2 2 0 (motivicMilnorSymbol k x) := rfl

/-- Level one vanishes in the actual finite motivic target. -/
theorem coefficient_one (x : MilnorK.K2.Group k) :
    finiteMilnorSymbolModulo k 1 (QuotientAddGroup.mk x) = 0 :=
  finiteMilnorSymbol_one k x

/-- Composite coefficient levels use the exact same reduced graph convention. -/
theorem coefficient_six (a b : kˣ) :
    finiteMilnorSymbolModulo k 6 (QuotientAddGroup.mk (symbol a b)) =
      motivicBaseIntegralReduction k 2 2 6
        ((motivicRawBaseEvaluationComparison k 2 2).symm
          (WeightTwoSymbols.graphSymbol k a b)) :=
  finiteMilnorSymbolModulo_symbol k 6 a b

variable {k} {L : Type u} [Field L] [CharZero L] (φ : k →+* L)

/-- Use the standard derived category of Nisnevich sheaves over the extension field in this test. -/
local instance instHasDerivedCategoryExtensionMotivicTest : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- Raw naturality uses the actual signed cochain map and original Milnor field map. -/
theorem actual_raw_naturality (x : MilnorK.K2.Group k) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
        (rawMilnorSymbol k x) = rawMilnorSymbol L (mapAdd φ x) :=
  rawMilnorSymbol_fieldChange φ x

/-- Integral naturality uses the actual cohomological field map. -/
theorem actual_derived_naturality :
    (motivicCohomologyFieldChange φ 2 2).comp (motivicMilnorSymbol k) =
      (motivicMilnorSymbol L).comp (mapAdd φ) :=
  motivicMilnorSymbol_fieldChange_square φ

/-- Finite naturality holds at every natural level, including zero and composite levels. -/
theorem actual_finite_naturality (n : ℕ) :
    (motivicFiniteCohomologyFieldChange φ 2 2 n).comp (finiteMilnorSymbol k n) =
      (finiteMilnorSymbol L n).comp (mapAdd φ) :=
  finiteMilnorSymbol_fieldChange_square φ n

/-- The exact modulo quotient also commutes with the original finite field-change map. -/
theorem actual_modulo_naturality (n : ℕ) :
    (motivicFiniteCohomologyFieldChange φ 2 2 n).comp (finiteMilnorSymbolModulo k n) =
      (finiteMilnorSymbolModulo L n).comp (milnorModuloFieldChange φ n) :=
  finiteMilnorSymbolModulo_fieldChange_square φ n

open Lean in
run_cmd do
  for name in #[``rawSymbolMap, ``rawMilnorSymbol, ``rawMilnorSymbol_symbol,
      ``rawMilnorSymbol_tensor_square, ``motivicMilnorSymbol,
      ``motivicMilnorSymbol_symbol, ``motivicMilnorSymbol_comparison,
      ``motivicMilnorSymbol_tensor_square, ``finiteMilnorSymbol,
      ``finiteMilnorSymbol_symbol, ``finiteMilnorSymbol_reduction_square,
      ``finiteMilnorSymbol_tensor_square, ``finiteMilnorSymbol_topDegree_comparison,
      ``nsmul_finiteMilnorSymbol, ``milnorMultiples_le_ker, ``finiteMilnorSymbolModulo,
      ``finiteMilnorSymbolModulo_symbol, ``finiteMilnorSymbolModulo_reduction_square,
      ``rawMilnorSymbol_fieldChange_square, ``motivicMilnorSymbol_fieldChange_square,
      ``finiteMilnorSymbol_fieldChange_square, ``milnorModuloFieldChange,
      ``finiteMilnorSymbolModulo_fieldChange_square,
      ``actual_raw_symbol, ``actual_raw_tensor_factorization, ``actual_raw_steinberg,
      ``actual_derived_symbol, ``actual_derived_tensor_factorization,
      ``actual_finite_symbol, ``actual_reduction_square, ``exact_milnor_multiples,
      ``actual_modulo_reduction_square, ``actual_top_degree_comparison,
      ``coefficient_zero, ``coefficient_one, ``coefficient_six,
      ``actual_raw_naturality, ``actual_derived_naturality,
      ``actual_finite_naturality, ``actual_modulo_naturality] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual Milnor descent, reduction, and field naturality use standard foundations."

end MotivicTest.WeightTwoMilnorSymbol
