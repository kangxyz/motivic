/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalPolynomialPointBaseChange
public import Motivic.Cohomology.Motivic.DiagonalFieldChange
public import Aglib.KTheory.MilnorK.Norm.Polynomial.FiniteComparison

/-! # Full-branch base change for original all-weight transferred Milnor symbols -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped BigOperators

universe u

namespace Motivic.DiagonalMilnorNormBaseChange

open MilnorK MilnorK.PolynomialResidue
open Polynomial.LocalResidue DiagonalMilnorSymbol DiagonalCorestriction

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [CharZero k] [CharZero L]

local instance polynomialFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance polynomialCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

/-- Every original scalar branch occurs, for every actual Milnor class and every weight. -/
theorem corestriction_rawSymbol_baseChange_algebraMap (n : ℕ) (p : MonicIrreducible k)
    (x : K (AdjoinRoot p.val) n) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) n) n
      (corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x)) =
      ∑ q ∈ (placesAbove (algebraMap k L) p).attach,
        corestriction (k := L) n (rawSymbol (AdjoinRoot q.val.val) n
          (map n (adjoinRootMap (algebraMap k L) p.val q.val.val
            ((mem_placesAbove (algebraMap k L) p q.val).mp q.property)) x)) := by
  classical
  have h : (HomologicalComplex.homologyMap
      (motivicRawBaseComplexMap (algebraMap k L) n) n).hom.comp
        ((corestriction (k := k) n).comp (rawSymbol (AdjoinRoot p.val) n)) =
      ∑ q ∈ (placesAbove (algebraMap k L) p).attach,
        (corestriction (k := L) n).comp
          ((rawSymbol (AdjoinRoot q.val.val) n).comp
            (map n (adjoinRootMap (algebraMap k L) p.val q.val.val
              ((mem_placesAbove (algebraMap k L) p q.val).mp q.property))).toAddMonoidHom) := by
    apply MilnorK.addHom_ext
    intro a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply,
      LinearMap.toAddMonoidHom_coe, map_symbol, rawSymbol_symbol]
    rw [corestriction_graphSymbol, DiagonalFieldChange.cycleClass_fieldChange,
      DiagonalCorestrictionBaseChange.pointPushforward_graph_baseChange_algebraMap]
    simp only [map_sum, corestriction_graphSymbol, Function.comp_def]
  exact (DFunLike.congr_fun h x).trans (by
    simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe])

/-- If the literal whole mapped polynomial is irreducible, the full branch sum has one term. -/
theorem corestriction_rawSymbol_baseChange_irreducible (n : ℕ)
    (p : MonicIrreducible k) (q : MonicIrreducible L)
    (hq : q.val = p.val.map (algebraMap k L)) (x : K (AdjoinRoot p.val) n) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) n) n
      (corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x)) =
      corestriction (k := L) n (rawSymbol (AdjoinRoot q.val) n
        (map n (adjoinRootMap (algebraMap k L) p.val q.val (hq ▸ dvd_rfl)) x)) := by
  classical
  rw [corestriction_rawSymbol_baseChange_algebraMap]
  have hmem : q ∈ placesAbove (algebraMap k L) p :=
    (mem_placesAbove (algebraMap k L) p q).mpr (hq ▸ dvd_rfl)
  let q' : {q // q ∈ placesAbove (algebraMap k L) p} := ⟨q, hmem⟩
  rw [Finset.sum_eq_single q']
  · intro r _ hr
    have heq : r = q' := Subtype.ext (by
      simpa only [PolynomialNorm.placesAbove_eq_singleton (algebraMap k L) p q hq,
        Finset.mem_singleton] using r.property)
    exact (hr heq).elim
  · intro h
    exact (h (Finset.mem_attach _ _)).elim

end Motivic.DiagonalMilnorNormBaseChange
