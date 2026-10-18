/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMonicDeformationNormSum
public import Lean.Util.CollectAxioms

/-!
# Repeated endpoint factors in the actual polynomial-norm multiset

Both polynomial coordinates are independent, and the whole square quotient is
kept. The finite multiset preserves every occurrence of every irreducible factor.
-/

@[expose] public noncomputable section

open Polynomial Motivic WeightTwoCorestriction WeightTwoMonicDeformation
open WeightTwoMonicDeformationFactors WeightTwoMilnorSymbol
open MilnorK.K3.PolynomialNorm MilnorK.K3.PolynomialResidue

universe u

namespace MotivicTest.WeightTwoMonicDeformationNormSum

variable {k : Type u} [Field k] [CharZero k]

local instance charZero_root (p : MonicIrreducible k) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- Repeated factors and independent polynomial units use the original multiset endpoint. -/
theorem repeated_factorPlaces_endpoint (p A B : k[X]) (hp : p.Monic)
    (hcop : IsCoprime (p ^ 2) (A * B)) (a b : (AdjoinRoot (p ^ 2))ˣ)
    (ha : (a : AdjoinRoot (p ^ 2)) = AdjoinRoot.mk (p ^ 2) A)
    (hb : (b : AdjoinRoot (p ^ 2)) = AdjoinRoot.mk (p ^ 2) B) :
    WeightTwoSymbols.cycleClass k (polynomialCycle (p ^ 2) (hp.pow 2) a b) =
      ((factorPlaces (p ^ 2) (hp.pow 2).ne_zero).attach.map fun
        (r : {r : MonicIrreducible k // r ∈ factorPlaces (p ^ 2) (hp.pow 2).ne_zero}) =>
        letI := r.val.property.1.finite_adjoinRoot
        corestriction (k := k) (E := AdjoinRoot r.val.val)
          (rawMilnorSymbol (AdjoinRoot r.val.val)
            (factorSymbol (p ^ 2) A B (hp.pow 2).ne_zero hcop r))).sum :=
  cycleClass_polynomialCycle_eq_factorPlaces (p ^ 2) A B (hp.pow 2) hcop a b ha hb

/-- The actual original family coordinates satisfy the required literal quotient equations. -/
theorem original_family_factorPlaces (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hcop : IsCoprime p (A * B)) :
    WeightTwoSymbols.cycleClass k (zeroCycle p A B γ hp hcop) =
      ((factorPlaces p hp.ne_zero).attach.map fun
        (r : {r : MonicIrreducible k // r ∈ factorPlaces p hp.ne_zero}) =>
        letI := r.val.property.1.finite_adjoinRoot
        corestriction (k := k) (E := AdjoinRoot r.val.val)
          (rawMilnorSymbol (AdjoinRoot r.val.val)
            (factorSymbol p A B hp.ne_zero hcop r))).sum :=
  cycleClass_polynomialCycle_eq_factorPlaces p A B hp hcop
    (zeroFirstUnit p A B γ hcop) (zeroSecondUnit p A B γ hcop)
    (zeroFirstUnit_val p A B γ hcop) (zeroSecondUnit_val p A B γ hcop)

open Lean in
run_cmd do
  for name in #[``branchUnit_eq_quotientUnit, ``cycleClass_polynomialCycle_eq_factorPlaces,
      ``repeated_factorPlaces_endpoint, ``original_family_factorPlaces] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole endpoint norm-indexed factor sums use only standard foundations."

end MotivicTest.WeightTwoMonicDeformationNormSum
