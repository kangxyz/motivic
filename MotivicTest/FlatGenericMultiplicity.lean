/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.FlatGenericMultiplicity
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Consumers of rank-free flat generic multiplicity

The actual localized base-change equivalence is checked on pure tensors.
A square-zero polynomial quotient over an arbitrary field exercises the
multiplicity formula with its full closed-fiber quotient retained. Neither
reducedness nor separability nor a rank/dimension equality is required.
-/

@[expose] public section

-- Nested quotient/localization scalar instances require three pending elaboration levels.
set_option maxSynthPendingDepth 3

open scoped TensorProduct Polynomial
open TensorProduct Module

universe u v w

namespace MotivicTest.FlatGenericMultiplicity

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The literal square-zero polynomial quotient used in the regression. -/
abbrev squareZeroAlgebra (k : Type u) [Field k] :=
  k[X] ⧸ Ideal.span {(Polynomial.X : k[X]) ^ 2}

/-- The base-change localization comparison uses the actual scalar action
on pure tensors, not an unlabelled module isomorphism. -/
theorem localizedPureTensor (M : Type w) [AddCommGroup M] [Module A M]
    (q : Ideal B) [q.IsPrime] (c : Localization.AtPrime q) (b : B) (m : M) :
    flatGenericLocalizedBaseChangeEquiv M q (c ⊗ₜ[B] (b ⊗ₜ[A] m)) = (b • c) ⊗ₜ[A] m :=
  AlgebraTensorModule.cancelBaseChange_tmul A B (Localization.AtPrime q) _ _ _

/-- Flat going down actually recovers the source generic point. -/
theorem genericContraction [Module.Flat A B] (I : Ideal A) (q : Ideal B) [q.IsPrime]
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) : q.under A ∈ I.minimalPrimes :=
  flatGeneric_under_mem_minimalPrimes I q hq

/-- The actual square-zero polynomial quotient is permitted as a target.
Its full closed-fiber factor remains in the formula for two coefficients. -/
theorem squareZeroTarget (k : Type u) [Field k]
    (q : Ideal (squareZeroAlgebra k)) [q.IsPrime]
    (hq : q ∈ (⊥ : Ideal (squareZeroAlgebra k)).minimalPrimes) :
    Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[squareZeroAlgebra k]
          ((squareZeroAlgebra k) ⊗[k] (k × k))) =
      Module.length (Localization.AtPrime (q.under k))
        (Localization.AtPrime (q.under k) ⊗[k] (k × k)) *
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ (q.under k).map (algebraMap k (Localization.AtPrime q))) := by
  apply flatGeneric_multiplicity (k × k) ⊥ bot_le q
  simpa only [Ideal.map_bot] using hq

/-- All three lengths of the actual square-zero-target example are finite,
without replacing the target quotient by its reduction. -/
theorem squareZeroTargetFinite (k : Type u) [Field k]
    (q : Ideal (squareZeroAlgebra k)) [q.IsPrime]
    (hq : q ∈ (⊥ : Ideal (squareZeroAlgebra k)).minimalPrimes) :
    Module.length (Localization.AtPrime (q.under k))
        (Localization.AtPrime (q.under k) ⊗[k] (k × k)) ≠ ⊤ ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[k] (k × k)) ≠ ⊤ ∧
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ (q.under k).map (algebraMap k (Localization.AtPrime q))) ≠ ⊤ := by
  apply flatGeneric_lengths_ne_top (k × k) ⊥ bot_le q
  simpa only [Ideal.map_bot] using hq

/-- The polynomial-quotient target above has an actual nonzero square-zero
element; the regression is not merely named as a nonreduced example. -/
theorem squareZeroTargetHasNilpotent (k : Type u) [Field k] :
    ∃ a : squareZeroAlgebra k, a ≠ 0 ∧ a ^ 2 = 0 := by
  let I : Ideal k[X] := Ideal.span {(Polynomial.X : k[X]) ^ 2}
  refine ⟨Ideal.Quotient.mk I Polynomial.X, ?_, ?_⟩
  · intro hz
    have hx : (Polynomial.X : k[X]) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hdvd : (Polynomial.X : k[X]) ^ 2 ∣ Polynomial.X :=
      Ideal.mem_span_singleton.mp hx
    have hc := Polynomial.X_pow_dvd_iff.mp hdvd 1 (by omega)
    simp at hc
  · rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- No separability or finite-degree premise is required by flat generic
multiplicity, even when the scalar map is an arbitrary extension of fields. -/
theorem arbitraryFieldExtension (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] :
    Module.length (Localization.AtPrime (⊥ : Ideal L))
        (Localization.AtPrime (⊥ : Ideal L) ⊗[L] (L ⊗[k] (k × k))) =
      Module.length (Localization.AtPrime ((⊥ : Ideal L).under k))
        (Localization.AtPrime ((⊥ : Ideal L).under k) ⊗[k] (k × k)) *
      Module.length (Localization.AtPrime (⊥ : Ideal L))
        (Localization.AtPrime (⊥ : Ideal L) ⧸ ((⊥ : Ideal L).under k).map
          (algebraMap k (Localization.AtPrime (⊥ : Ideal L)))) := by
  apply flatGeneric_multiplicity (k × k) ⊥ bot_le (⊥ : Ideal L)
  rw [Ideal.map_bot, Ideal.minimalPrimes_eq_subsingleton_self]
  simp

end MotivicTest.FlatGenericMultiplicity
