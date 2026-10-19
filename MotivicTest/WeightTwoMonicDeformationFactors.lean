/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.MonicDeformationFactors
public import Lean.Util.CollectAxioms

/-!
# Consumers of original factor-field endpoint transfers

The finite corestrictions use literal monic factor quotients and actual unit
images. The coefficient is the full count in the normalized-factor multiset.
-/

@[expose] public noncomputable section

open Polynomial Motivic WeightTwoCorestriction WeightTwoMonicDeformation
open WeightTwoMonicDeformationFactors UniqueFactorizationMonoid
open scoped BigOperators

universe u

namespace MotivicTest.WeightTwoMonicDeformationFactors

variable {k : Type u} [Field k]

open scoped Classical in
/-- Repeated-factor coefficients multiply the original quotient-field transfer. -/
theorem actual_factor_counts (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    letI : Fintype (AdjoinRoot.IrreducibleBranch p) :=
      Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p))
        (AdjoinRoot.branchEquivMaximal p hp.ne_zero).symm
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) =
      ∑ q : AdjoinRoot.IrreducibleBranch p,
        letI := q.val.property.1.finite_adjoinRoot
        ((normalizedFactors p).count q.val.val : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot q.val.val)
            (Units.map (AdjoinRoot.divisorMap p q.val.val q.property).toMonoidHom a)
            (Units.map (AdjoinRoot.divisorMap p q.val.val q.property).toMonoidHom b)) :=
  cycleClass_polynomialCycle_eq_sum_factor_counts p hp a b

/-- The irreducible input is literally its original field transfer. -/
theorem original_irreducible_endpoint (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) =
      corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p) a b) :=
  cycleClass_polynomialCycle_irreducible p hp a b

open Lean in
run_cmd do
  for name in #[``pointPushforward_graph_algEquiv, ``corestriction_graphSymbol_algEquiv,
      ``branchQuotientAlgEquiv_residueUnit, ``corestriction_residueUnit_branch,
      ``cycleClass_polynomialCycle_eq_sum_branches,
      ``cycleClass_polynomialCycle_eq_sum_factor_counts,
      ``cycleClass_polynomialCycle_irreducible,
      ``actual_factor_counts, ``original_irreducible_endpoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Literal factor-field endpoint transfers use only standard foundations."

end MotivicTest.WeightTwoMonicDeformationFactors
