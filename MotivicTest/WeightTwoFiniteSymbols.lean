/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.FiniteSymbols
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual finite weight-two symbols

These consumers check the original coefficient reduction and quotient
comparison at arbitrary natural levels, composite-level annihilation, and
level-one vanishing. The axiom audit rejects nonstandard assumptions.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic Motivic.WeightTwoFiniteSymbols
open scoped TensorProduct

universe w u

namespace MotivicTest.WeightTwoFiniteSymbols

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The finite target is the original derived motivic group. -/
def actual_finite_symbol (n : ℕ) : (Additive kˣ ⊗[ℤ] Additive kˣ) →+
    motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k))) :=
  finiteTensorSymbol k n

/-- The original integral reduction is retained on every tensor. -/
theorem original_reduction (n : ℕ) (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    actual_finite_symbol k n x =
      motivicBaseIntegralReduction k 2 2 n (WeightTwoSymbols.motivicTensorSymbol k x) :=
  finiteTensorSymbol_eq_reduction k n x

/-- The original rational graph is retained on tensor generators. -/
theorem original_graph_reduction (n : ℕ) (a b : kˣ) :
    actual_finite_symbol k n (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) =
      motivicBaseIntegralReduction k 2 2 n
        ((motivicRawBaseEvaluationComparison k 2 2).symm
          (WeightTwoSymbols.graphSymbol k a b)) :=
  finiteTensorSymbol_tmul k n a b

/-- The quotient comparison has precisely the integral symbol's coset. -/
theorem original_quotient (n : ℕ) (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    FieldTopDegree.topDegreeFiniteEquiv k 2 n (actual_finite_symbol k n x) =
      (QuotientAddGroup.mk (WeightTwoSymbols.motivicTensorSymbol k x) :
        FieldTopDegree.integralModulo k 2 n) :=
  finiteTensorSymbol_topDegree_comparison k n x

/-- Composite levels require no prime or characteristic assumption. -/
theorem composite_annihilation (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    6 • actual_finite_symbol k 6 x = 0 :=
  nsmul_finiteTensorSymbol k 6 x

/-- The level-one symbol is zero in the original finite target. -/
theorem level_one (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    actual_finite_symbol k 1 x = 0 :=
  finiteTensorSymbol_one k x

open Lean in
run_cmd do
  for name in #[``finiteTensorSymbol, ``finiteTensorSymbol_eq_reduction,
      ``finiteTensorSymbol_tmul, ``finiteTensorSymbol_cone_comparison,
      ``finiteTensorSymbol_topDegree_comparison, ``nsmul_finiteTensorSymbol,
      ``finiteTensorSymbol_one, ``actual_finite_symbol, ``original_reduction,
      ``original_graph_reduction, ``original_quotient, ``composite_annihilation,
      ``level_one] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite weight-two symbols use only standard Lean foundations."

end MotivicTest.WeightTwoFiniteSymbols
