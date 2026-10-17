/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoFieldChange
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual weight-two symbol naturality

These consumers retain the original raw graph, integral tensor symbol, finite
reduction, and actual cohomological field maps. The tensor map is the ordinary
unit map in each factor. Coefficient levels include zero, composite levels,
and the characteristic. The axiom audit rejects nonstandard assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.WeightTwoSymbols Motivic.WeightTwoFiniteSymbols Motivic.WeightTwoFieldChange
open scoped TensorProduct

universe w u

namespace MotivicTest.WeightTwoFieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The original signed cochain map retains the literal two-coordinate graph class. -/
theorem original_raw_graph (a b : kˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2 (graphSymbol k a b) =
      graphSymbol L (Units.map φ.toMonoidHom a) (Units.map φ.toMonoidHom b) :=
  graphSymbol_fieldChange φ a b

/-- The ordinary tensor map has no inverse twist in either coordinate. -/
theorem ordinary_tensor_map (a b : kˣ) :
    unitsTensorFieldChange φ (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) =
      Additive.ofMul (Units.map φ.toMonoidHom a) ⊗ₜ[ℤ]
        Additive.ofMul (Units.map φ.toMonoidHom b) :=
  unitsTensorFieldChange_tmul φ a b

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The actual integral field map carries the original derived graph class. -/
theorem original_integral_graph (a b : kˣ) :
    motivicCohomologyFieldChange φ 2 2
        ((motivicRawBaseEvaluationComparison k 2 2).symm (graphSymbol k a b)) =
      (motivicRawBaseEvaluationComparison L 2 2).symm
        (graphSymbol L (Units.map φ.toMonoidHom a) (Units.map φ.toMonoidHom b)) :=
  motivicGraphSymbol_fieldChange φ a b

/-- Naturality concerns the original tensor symbol and actual derived field map. -/
theorem original_integral_tensor (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    motivicCohomologyFieldChange φ 2 2 (motivicTensorSymbol k x) =
      motivicTensorSymbol L (unitsTensorFieldChange φ x) :=
  motivicTensorSymbol_fieldChange φ x

/-- Every finite symbol is natural through its original integral reduction. -/
theorem original_finite_reduction (n : ℕ) (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    motivicFiniteCohomologyFieldChange φ 2 2 n
        (motivicBaseIntegralReduction k 2 2 n (motivicTensorSymbol k x)) =
      motivicBaseIntegralReduction L 2 2 n
        (motivicTensorSymbol L (unitsTensorFieldChange φ x)) :=
  finiteTensorSymbol_fieldChange φ n x

/-- The finite commuting square is an equality of the original additive maps. -/
theorem original_finite_square (n : ℕ) :
    (motivicFiniteCohomologyFieldChange φ 2 2 n).comp (finiteTensorSymbol k n) =
      (finiteTensorSymbol L n).comp (unitsTensorFieldChange φ) :=
  finiteTensorSymbol_fieldChange_square φ n

/-- Zero coefficient level is included without an invertibility premise. -/
theorem coefficient_zero (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    motivicFiniteCohomologyFieldChange φ 2 2 0 (finiteTensorSymbol k 0 x) =
      finiteTensorSymbol L 0 (unitsTensorFieldChange φ x) :=
  finiteTensorSymbol_fieldChange φ 0 x

/-- Composite coefficient level retains the same ordinary unit images. -/
theorem coefficient_six (a b : kˣ) :
    motivicFiniteCohomologyFieldChange φ 2 2 6
        (finiteTensorSymbol k 6 (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) =
      finiteTensorSymbol L 6
        (Additive.ofMul (Units.map φ.toMonoidHom a) ⊗ₜ[ℤ]
          Additive.ofMul (Units.map φ.toMonoidHom b)) :=
  finiteTensorSymbol_tmul_fieldChange φ 6 a b

/-- The same naturality applies when the coefficient level equals the characteristic. -/
theorem characteristic_two
    [HasDerivedCategory.{w}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (ZMod 2)))) AddCommGrpCat.{1})]
    (ψ : ZMod 2 →+* ZMod 2) (a b : (ZMod 2)ˣ) :
    motivicFiniteCohomologyFieldChange ψ 2 2 2
        (finiteTensorSymbol (ZMod 2) 2 (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) =
      finiteTensorSymbol (ZMod 2) 2
        (Additive.ofMul (Units.map ψ.toMonoidHom a) ⊗ₜ[ℤ]
          Additive.ofMul (Units.map ψ.toMonoidHom b)) :=
  finiteTensorSymbol_tmul_fieldChange ψ 2 a b

open Lean in
run_cmd do
  for name in #[``rationalTorusPoint_coefficient, ``rationalTorusPoint_fieldChange,
      ``rationalPair_fieldChange, ``rationalGraph_fieldChange, ``rawClass_fieldChange,
      ``singularClass_fieldChange, ``cycleClass_fieldChange, ``graphSymbol_fieldChange,
      ``unitsTensorFieldChange, ``unitsTensorFieldChange_tmul, ``tensorSymbol_fieldChange,
      ``motivicGraphSymbol_fieldChange, ``motivicTensorSymbol_fieldChange,
      ``motivicTensorSymbol_fieldChange_square, ``finiteTensorSymbol_fieldChange,
      ``finiteTensorSymbol_fieldChange_square, ``finiteTensorSymbol_tmul_fieldChange,
      ``original_raw_graph, ``ordinary_tensor_map, ``original_integral_graph,
      ``original_integral_tensor, ``original_finite_reduction, ``original_finite_square,
      ``coefficient_zero, ``coefficient_six, ``characteristic_two] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-two field-change naturality uses only standard Lean foundations."

end MotivicTest.WeightTwoFieldChange
