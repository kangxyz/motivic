/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCorestrictionMixed
public import Motivic.Cohomology.Motivic.DiagonalMilnorSymbol
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.One

/-! # Genuine all-weight mixed Milnor/motivic transfer compatibility -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Additive

universe w u

namespace Motivic.DiagonalMilnorMixedNorm

open MilnorK DiagonalMilnorSymbol DiagonalCorestrictionMixed

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [Module.Finite k E] [CharZero k] [CharZero E]

omit [CharZero k] [CharZero E] in
/-- The actual graph transfer norm law in the literal final slot. -/
theorem corestriction_graphSymbol_snoc (n : ℕ) (a : Fin n → kˣ) (b : Eˣ) :
    DiagonalCorestriction.corestriction (k := k) (n + 1)
      (DiagonalCycleSymbols.graphSymbol E (n + 1)
        (Fin.snoc (fun i => Units.map (algebraMap k E).toMonoidHom (a i)) b)) =
      DiagonalCycleSymbols.graphSymbol k (n + 1)
        (Fin.snoc a (Units.map (Algebra.norm k) b)) := by
  have h := corestriction_graphSymbol_varying (n + 1) (Fin.snoc a 1) (Fin.last n) b
  have he : mixedTuple (n + 1) (Fin.snoc a 1) (Fin.last n) b =
      Fin.snoc (fun i => Units.map (algebraMap k E).toMonoidHom (a i)) b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [mixedTuple]
    · simp [mixedTuple, Fin.castSucc_ne_last]
  have hk : Function.update (Fin.snoc a 1 : Fin (n + 1) → kˣ)
      (Fin.last n) (Units.map (Algebra.norm k) b) =
      Fin.snoc a (Units.map (Algebra.norm k) b) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.castSucc_ne_last]
  rw [he, hk] at h
  exact h

/-- The original all-weight raw symbol intertwines both actual norms on mixed generators. -/
theorem raw_mixed_symbol (n : ℕ) (a : Fin n → kˣ) (b : Eˣ) :
    rawSymbol k (n + 1) (finiteExtensionNorm k E (n + 1)
      (productUnit n (map n (algebraMap k E) (symbol a)) (ofMul b))) =
    DiagonalCorestriction.corestriction (k := k) (n + 1)
      (rawSymbol E (n + 1)
        (productUnit n (map n (algebraMap k E) (symbol a)) (ofMul b))) := by
  rw [finiteExtensionNorm_productUnit_constants, map_symbol]
  simp only [productUnit_symbol, toMul_ofMul, rawSymbol_symbol]
  exact (corestriction_graphSymbol_snoc n a b).symm

/-- The same norm comparison holds for every base Milnor class, not only symbols. -/
theorem raw_mixed (n : ℕ) (x : K k n) (b : Eˣ) :
    rawSymbol k (n + 1) (finiteExtensionNorm k E (n + 1)
      (productUnit n (map n (algebraMap k E) x) (ofMul b))) =
    DiagonalCorestriction.corestriction (k := k) (n + 1)
      (rawSymbol E (n + 1)
        (productUnit n (map n (algebraMap k E) x) (ofMul b))) := by
  let f := (((productUnit n).flip (ofMul b)).comp (map n (algebraMap k E))).toAddMonoidHom
  have h : (rawSymbol k (n + 1)).comp
      ((finiteExtensionNorm k E (n + 1)).toAddMonoidHom.comp f) =
      (DiagonalCorestriction.corestriction (k := k) (n + 1)).comp
        ((rawSymbol E (n + 1)).comp f) := by
    apply addHom_ext
    intro a
    exact raw_mixed_symbol n a b
  exact DFunLike.congr_fun h x

section Derived

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The same mixed comparison is in the original derived diagonal motivic group. -/
theorem derived_mixed (n : ℕ) (x : K k n) (b : Eˣ) :
    motivicSymbol k (n + 1) (finiteExtensionNorm k E (n + 1)
      (productUnit n (map n (algebraMap k E) x) (ofMul b))) =
    DiagonalCorestriction.motivicCorestriction (k := k) (n + 1)
      (motivicSymbol E (n + 1)
        (productUnit n (map n (algebraMap k E) x) (ofMul b))) := by
  apply (motivicRawBaseEvaluationComparison k ((n + 1 : ℕ) : ℤ) (n + 1)).injective
  rw [motivicSymbol_comparison, DiagonalCorestriction.motivicCorestriction_comparison,
    motivicSymbol_comparison, raw_mixed]

end Derived

end Motivic.DiagonalMilnorMixedNorm
