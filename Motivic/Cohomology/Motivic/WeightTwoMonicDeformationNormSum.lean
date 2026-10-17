/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMonicDeformationFactors
public import Motivic.Cohomology.Motivic.WeightTwoMilnorSymbol
public import Motivic.KTheory.MilnorK3.PolynomialNormDeformation

/-!
# The complete endpoint sum in the original polynomial norm indexing

The exact local-length decomposition is the full normalized-factor multiset
used by the actual polynomial norm. Each summand is the original raw Milnor
symbol of the actual quotient units, followed by the actual finite corestriction.
No compatibility with Milnor norms is assumed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped BigOperators

universe u

namespace Motivic.WeightTwoMonicDeformationFactors

open WeightTwoCorestriction WeightTwoMonicDeformation WeightTwoMilnorSymbol
open KTheory.MilnorK3.PolynomialNorm KTheory.MilnorK3.PolynomialResidue
open UniqueFactorizationMonoid

variable {k : Type u} [Field k]

local instance charZero_root [CharZero k] (p : MonicIrreducible k) :
    CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- A polynomial coordinate transports to its literal quotient unit in every factor field. -/
theorem branchUnit_eq_quotientUnit (p A : k[X]) (a : (AdjoinRoot p)ˣ)
    (ha : (a : AdjoinRoot p) = AdjoinRoot.mk p A)
    (q : AdjoinRoot.IrreducibleBranch p) (hA : ¬ q.val.val ∣ A) :
    branchUnit p a q = quotientUnit q.val.val A hA := by
  apply Units.ext
  change AdjoinRoot.divisorMap p q.val.val q.property a = AdjoinRoot.mk q.val.val A
  rw [ha, AdjoinRoot.divisorMap_mk]

/-- The whole endpoint uses exactly the same multiplicity-preserving factor multiset
and literal quotient symbols as the actual polynomial norm construction. -/
theorem cycleClass_polynomialCycle_eq_factorPlaces [CharZero k] (p A B : k[X]) (hp : p.Monic)
    (hcop : IsCoprime p (A * B)) (a b : (AdjoinRoot p)ˣ)
    (ha : (a : AdjoinRoot p) = AdjoinRoot.mk p A)
    (hb : (b : AdjoinRoot p) = AdjoinRoot.mk p B) :
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) =
      ((factorPlaces p hp.ne_zero).attach.map fun
        (r : {r : MonicIrreducible k // r ∈ factorPlaces p hp.ne_zero}) =>
        letI := r.val.property.1.finite_adjoinRoot
        corestriction (k := k) (E := AdjoinRoot r.val.val)
          (rawMilnorSymbol (AdjoinRoot r.val.val)
          (factorSymbol p A B hp.ne_zero hcop r))).sum := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let : Fintype (AdjoinRoot.IrreducibleBranch p) :=
    Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p))
      (AdjoinRoot.branchEquivMaximal p hp.ne_zero).symm
  let g (q : AdjoinRoot.IrreducibleBranch p) : rawH22 k :=
    letI := q.val.property.1.finite_adjoinRoot
    corestriction (k := k) (E := AdjoinRoot q.val.val)
      (rawMilnorSymbol (AdjoinRoot q.val.val)
      (factorSymbol p A B hp.ne_zero hcop
        ⟨q.val, (mem_factorPlaces_iff p hp.ne_zero q.val).mpr q.property⟩))
  rw [cycleClass_polynomialCycle_eq_sum_factor_counts]
  calc
    _ = ∑ q : AdjoinRoot.IrreducibleBranch p,
        (normalizedFactors p).count q.val.val • g q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Nat.cast_smul_eq_nsmul]
      congr 1
      dsimp only [g, factorSymbol]
      rw [rawMilnorSymbol_symbol,
        branchUnit_eq_quotientUnit p A a ha q,
        branchUnit_eq_quotientUnit p B b hb q]
    _ = _ := (factorPlaces_sum_eq_sum_count p hp.ne_zero g).symm

end Motivic.WeightTwoMonicDeformationFactors
