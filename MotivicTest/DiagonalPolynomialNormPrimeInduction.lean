/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.PolynomialNormPrimeInduction
public import Motivic.Cohomology.Diagonal.RestrictionSylow
public import Lean.Util.CollectAxioms

/-! The genuine prime comparison step retains its strict lower-degree premise. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open DiagonalMilnorSymbol
open DiagonalCorestriction
open MilnorK.PolynomialResidue MilnorK.PolynomialNorm
open DiagonalPolynomialNormInduction
universe u
namespace MotivicTest.DiagonalPolynomialNormPrimeInduction
variable {k : Type u} [Field k] [CharZero k]
local instance rootFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
local instance rootCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

/-- The actual original symbol and transfer are compared, without normality. -/
theorem actual_prime_step (n : ℕ) (p : MonicIrreducible k)
    (hp : p.val.natDegree.Prime)
    (ih : ∀ (r : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol (AdjoinRoot p.val) n (polynomialNorm n r y) =
          corestriction (k := AdjoinRoot p.val) n (rawSymbol (AdjoinRoot r.val) n y))
    (x : MilnorK.K (AdjoinRoot p.val) n) :
    rawSymbol k n (polynomialNorm n p x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x) :=
  rawSymbol_polynomialNorm_prime_of_lower_degrees n p hp ih x

open Lean in
run_cmd do
  for name in #[``actual_prime_step, ``rawSymbol_polynomialNorm_zero,
      ``restriction_comparison_of_lower_degrees, ``degree_smul_comparison_defect_eq_zero,
      ``DiagonalRestrictionSylow.eq_of_sylow_restrictions] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual prime comparison induction and Sylow detection: standard foundations only."

end MotivicTest.DiagonalPolynomialNormPrimeInduction
