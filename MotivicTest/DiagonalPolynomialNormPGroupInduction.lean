/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalPolynomialNormPGroupInduction
public import Lean.Util.CollectAxioms

/-!
# Consumers of the genuine p-group norm-symbol induction step

The only comparison assumption is the explicit strong induction hypothesis on
strictly smaller polynomial degrees at the same fixed Milnor weight. Both the
original root polynomial and its embedding into the genuine ambient field are
retained. Every tested declaration is recursively audited for foundations.
-/

@[expose] public noncomputable section

universe u

namespace MotivicTest.DiagonalPolynomialNormPGroupInduction

open Motivic Motivic.DiagonalMilnorSymbol Motivic.DiagonalCorestriction
open Motivic.DiagonalPolynomialNormInduction Motivic.KTheory
open MilnorK.PolynomialResidue MilnorK.PolynomialNorm

local instance testRootFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance testRootCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

variable {k Ω : Type u} [Field k] [CharZero k] [Field Ω]
  [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The original actual norm and transfer compare in a p-group ambient, and
only strict smaller-degree comparisons are supplied by the consumer. -/
theorem actual_pGroup_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω))
    (n d : ℕ) (p : MonicIrreducible k) (hd : p.val.natDegree ≤ d)
    (g : AdjoinRoot p.val →ₐ[k] Ω)
    (ih : ∀ (L : Type u) [Field L] [CharZero L] (r : MonicIrreducible L),
      r.val.natDegree < d → ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol L n (polynomialNorm n r y) =
          corestriction (k := L) n (rawSymbol (AdjoinRoot r.val) n y))
    (x : MilnorK.K (AdjoinRoot p.val) n) :
    rawSymbol k n (polynomialNorm n p x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x) :=
  rawSymbol_polynomialNorm_of_pGroup_of_lower_degrees ℓ hG n d p hd g ih x

/-- The degree-one base case is unconditional in every Milnor weight. -/
theorem actual_linear_comparison (n : ℕ) (p : MonicIrreducible k)
    (hp : p.val.natDegree = 1) (x : MilnorK.K (AdjoinRoot p.val) n) :
    rawSymbol k n (polynomialNorm n p x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x) :=
  rawSymbol_polynomialNorm_of_degree_one n p hp x

/-- A known comparison transports to an arbitrary original finite extension. -/
theorem actual_field_comparison_from_presentation
    {E : Type u} [Field E] [CharZero E] [Algebra k E] [FiniteDimensional k E]
    (n : ℕ) (p : MonicIrreducible k) (ε : AdjoinRoot p.val ≃ₐ[k] E)
    (h : ∀ y : MilnorK.K (AdjoinRoot p.val) n,
      rawSymbol k n (polynomialNorm n p y) =
        corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n y))
    (x : MilnorK.K E n) :
    rawSymbol k n (MilnorK.finiteExtensionNorm k E n x) =
      corestriction (k := k) n (rawSymbol E n x) :=
  rawSymbol_finiteExtensionNorm_of_presentation n p ε h x

open Lean in
run_cmd do
  for name in #[``rawSymbol_finiteExtensionNorm_of_presentation,
      ``rawSymbol_finiteExtensionNorm_of_lower_degrees,
      ``rawSymbol_polynomialNorm_of_degree_one,
      ``rawSymbol_polynomialNorm_of_pGroup_of_lower_degrees,
      ``actual_pGroup_comparison, ``actual_linear_comparison,
      ``actual_field_comparison_from_presentation] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual p-group norm-symbol induction uses only standard foundations."

end MotivicTest.DiagonalPolynomialNormPGroupInduction
