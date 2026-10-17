/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorNormBaseChange
public import Motivic.Cohomology.Motivic.DiagonalMilnorMixedNorm
public import Motivic.KTheory.MilnorK.FiniteExtensionNormBaseChange

/-! # Prime-to-prime restriction of the actual all-weight norm comparison -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Additive

universe u

namespace Motivic.DiagonalMilnorCoprimeRestriction

open KTheory.MilnorK KTheory.MilnorK.PolynomialResidue
open KTheory.MilnorK.PolynomialNorm Polynomial.LocalResidue DiagonalMilnorSymbol

variable {k : Type u} [Field k] [CharZero k]

local instance rootFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance rootCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

/-- Every mixed symbol has the actual polynomial/motivic norm comparison. -/
theorem raw_polynomial_mixed (p : MonicIrreducible k) (m : ℕ)
    (a : SymbolTuple k m) (b : (AdjoinRoot p.val)ˣ) :
    rawSymbol k (m + 1) (polynomialNorm (m + 1) p
      (symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b))) =
    DiagonalCorestriction.corestriction (k := k) (m + 1)
      (rawSymbol (AdjoinRoot p.val) (m + 1)
        (symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b))) := by
  have h := DiagonalMilnorMixedNorm.raw_mixed_symbol (k := k) m a b
  rw [finiteExtensionNorm_adjoinRoot, map_symbol] at h
  simpa only [productUnit_symbol, toMul_ofMul, Function.comp_def] using h

/-- A classwise finite prime-to-prime extension kills the original transfer-symbol discrepancy.
The mapped polynomial is retained literally, and its irreducibility comes from coprime degrees. -/
theorem exists_coprime_restriction_norm_eq (p : MonicIrreducible k)
    (hp : p.val.natDegree.Prime) (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) (m + 1))
          ((m + 1 : ℕ) : ℤ) (rawSymbol k (m + 1) (polynomialNorm (m + 1) p x)) =
        HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) (m + 1))
          ((m + 1 : ℕ) : ℤ) (DiagonalCorestriction.corestriction (k := k) (m + 1)
            (rawSymbol (AdjoinRoot p.val) (m + 1) x)) := by
  obtain ⟨L, hL, hA, hfd, hsep, hcop, q, hq, hdiv, c, hc⟩ :=
    exists_finite_coprime_mixed_expansion p hp m x
  let := hfd
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  refine ⟨L, hL, hA, hfd, hsep, hcop, ?_⟩
  rw [DiagonalFieldChange.rawSymbol_fieldChange,
    polynomialNorm_restrict_irreducible (algebraMap k L) (m + 1) p q hq,
    DiagonalMilnorNormBaseChange.corestriction_rawSymbol_baseChange_irreducible
      (m + 1) p q hq]
  rw [← hc]
  simp only [map_finsuppSum, map_zsmul]
  apply Finset.sum_congr rfl
  intro ab _
  dsimp only
  rw [raw_polynomial_mixed]

end Motivic.DiagonalMilnorCoprimeRestriction
