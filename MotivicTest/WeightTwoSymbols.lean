/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSymbols
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of genuine bilinear weight-two symbols

These consumers retain the actual reduced-cycle and derived motivic targets.
They check both multiplicative relations, including repeated roots in positive
characteristic, and reject all assumptions beyond standard Lean foundations.
They do not assert Steinberg descent or an integral Milnor comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.WeightTwoSymbols
open scoped TensorProduct

universe w u

namespace MotivicTest.WeightTwoSymbols

variable (k : Type u) [Field k]

/-- The left unit law is a relation of actual rational graph classes. -/
theorem original_left_relation (a b c : kˣ) :
    graphSymbol k (a * b) c = graphSymbol k a c + graphSymbol k b c :=
  graphSymbol_mul_left k a b c

/-- The right unit law is a relation of actual rational graph classes. -/
theorem original_right_relation (a b c : kˣ) :
    graphSymbol k a (b * c) = graphSymbol k a b + graphSymbol k a c :=
  graphSymbol_mul_right k a b c

/-- Coincident quadratic roots in characteristic two are included. -/
example (a b : (ZMod 2)ˣ) :
    graphSymbol (ZMod 2) (a * a) b = graphSymbol (ZMod 2) a b + graphSymbol (ZMod 2) a b :=
  graphSymbol_mul_left (ZMod 2) a a b

/-- Both original geometric identity axes vanish. -/
theorem original_axes (a : kˣ) : graphSymbol k 1 a = 0 ∧ graphSymbol k a 1 = 0 :=
  ⟨graphSymbol_one_left k a, graphSymbol_one_right k a⟩

/-- The tensor homomorphism retains the exact original graph representative. -/
theorem original_tensor_generator (a b : kˣ) :
    tensorSymbol k (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) = graphSymbol k a b :=
  tensorSymbol_tmul k _ _

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The tensor map lands in the originally defined derived motivic group. -/
def actual_derived_tensor_symbol :
    (Additive kˣ ⊗[ℤ] Additive kˣ) →+
      motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k))) :=
  motivicTensorSymbol k

/-- The derived comparison carries the symbol back to its original graph class. -/
theorem original_derived_graph (a b : kˣ) :
    motivicRawBaseEvaluationComparison k 2 2
      (actual_derived_tensor_symbol k (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) =
      graphSymbol k a b := by
  exact motivicTensorSymbol_tmul_comparison k a b

open Lean in
run_cmd do
  for name in #[``raw_outgoing_d_zero, ``rawClass, ``differential_rawClass,
      ``raw_d_one_two, ``singular_d_one_zero, ``singularClass,
      ``singularClass_boundary, ``cycleClass, ``singularClass_quotient,
      ``singularClass_face_quotient, ``cycleClass_endpoints, ``cycleClass_axis,
      ``rationalPair, ``appendUnit, ``prependUnit, ``rationalPoint_toBase,
      ``rationalPoint_appendUnit, ``rationalPoint_prependUnit, ``graphSymbol,
      ``rationalTorusPoint_one, ``rationalPair_one_left, ``rationalPair_one_right,
      ``graphSymbol_one_left, ``graphSymbol_one_right, ``cycleClass_quadratic_postcompose,
      ``graphSymbol_mul_left, ``graphSymbol_mul_right, ``graphSymbolRightHom, ``graphSymbolHom,
      ``tensorSymbol, ``tensorSymbol_tmul, ``motivicTensorSymbol,
      ``motivicTensorSymbol_tmul_comparison, ``original_left_relation,
      ``original_right_relation, ``original_axes, ``original_tensor_generator,
      ``actual_derived_tensor_symbol, ``original_derived_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual bilinear weight-two symbols use only standard Lean foundations."

end MotivicTest.WeightTwoSymbols
