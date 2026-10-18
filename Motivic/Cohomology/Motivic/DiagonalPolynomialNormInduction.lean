/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorNormBaseChange
public import Motivic.Cohomology.Motivic.DiagonalCorestrictionDegree
public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeInduction

/-!
# Actual diagonal norm comparison under strict lower-degree induction

The root-field restriction uses every original scalar branch. Each branch is
strictly smaller because the original polynomial already has a root there.
The stated induction hypothesis is comparison with the genuine raw symbol,
not a hidden general norm law or a conclusion inferred from its retraction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic.DiagonalPolynomialNormInduction
open PresheafWithTransfers DiagonalMilnorSymbol DiagonalCorestriction
open MilnorK.PolynomialResidue MilnorK.PolynomialNorm
open Polynomial Polynomial.LocalResidue AdjoinRoot
variable {k L : Type u} [Field k] [Field L] [CharZero k] [CharZero L] [Algebra k L]

local instance polynomialFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance rootCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

/-- A field containing the original root field kills the comparison defect under
precisely the lower-degree comparison hypothesis on that coefficient field. -/
theorem restriction_comparison_of_lower_degrees
    (n : ℕ) (p : MonicIrreducible k) (hp : 1 < p.val.natDegree)
    (f : AdjoinRoot p.val →ₐ[k] L)
    (ih : ∀ (r : MonicIrreducible L), r.val.natDegree < p.val.natDegree →
      ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol L n (polynomialNorm n r y) =
          corestriction (k := L) n (rawSymbol (AdjoinRoot r.val) n y))
    (x : MilnorK.K (AdjoinRoot p.val) n) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) n) n
        (rawSymbol k n (polynomialNorm n p x)) =
      HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) n) n
        (corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x)) := by
  classical
  rw [DiagonalFieldChange.rawSymbol_fieldChange, polynomialNorm_restrict,
    DiagonalMilnorNormBaseChange.corestriction_rawSymbol_baseChange_algebraMap]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact ih r.val
    (scalarBranch_natDegree_lt_of_rootHom p.val p.property.1 hp f
      ⟨r.val, (mem_placesAbove (algebraMap k L) p r.val).mp r.property⟩) _

/-- The original extension degree annihilates the actual diagonal comparison
failure. No normality is required, and the strict induction premise stays explicit. -/
theorem degree_smul_comparison_defect_eq_zero
    (n : ℕ) (p : MonicIrreducible k) (hp : 1 < p.val.natDegree)
    (ih : ∀ (r : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol (AdjoinRoot p.val) n (polynomialNorm n r y) =
          corestriction (k := AdjoinRoot p.val) n (rawSymbol (AdjoinRoot r.val) n y))
    (x : MilnorK.K (AdjoinRoot p.val) n) :
    (p.val.natDegree : ℤ) •
      (rawSymbol k n (polynomialNorm n p x) -
        corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x)) = 0 := by
  have h := restriction_comparison_of_lower_degrees n p hp
    (AlgHom.id k (AdjoinRoot p.val)) ih x
  have ht := congrArg (corestriction (k := k) (E := AdjoinRoot p.val) n) h
  rw [corestriction_fieldChange, corestriction_fieldChange] at ht
  have hd : Module.finrank k (AdjoinRoot p.val) = p.val.natDegree := by
    rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  rw [hd] at ht
  rw [smul_sub, ht, sub_self]

end Motivic.DiagonalPolynomialNormInduction
