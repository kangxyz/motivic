/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Dimension drops under a strict inclusion of prime ideals

An element of the larger prime outside the smaller one becomes a nonzero
divisor in the smaller prime quotient and is killed by the quotient factor
map. The surjective-map dimension inequality gives the dimension drop.
No Noetherian, local, catenary, or equidimensional hypothesis is needed.
-/

@[expose] public section

universe u

namespace Module

variable {R : Type u} [CommRing R]

/-- Strict prime inclusion lowers quotient dimension by at least one.
The proof uses a literal surjective quotient factor and a killed nonzero
divisor, rather than a catenary or expected-dimension hypothesis. -/
theorem strictPrime_quotient_dimension (p q : Ideal R) [p.IsPrime] (hpq : p < q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨a, haq, hap⟩ := Set.exists_of_ssubset hpq
  apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
    (Ideal.Quotient.factor_surjective hpq.le) (r := Ideal.Quotient.mk p a)
  · apply mem_nonZeroDivisors_iff_ne_zero.mpr
    exact fun hz => hap ((Ideal.Quotient.eq_zero_iff_mem).mp hz)
  · rw [Ideal.Quotient.factor_mk]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr haq

/-- The same strict-prime inequality in the coefficient support dimension
used by actual Koszul dimension vanishing. -/
theorem strictPrime_support_dimension (p q : Ideal R) [p.IsPrime] (hpq : p < q) :
    Module.supportDim R (R ⧸ q) + 1 ≤ Module.supportDim R (R ⧸ p) := by
  simpa only [Module.supportDim_quotient_eq_ringKrullDim] using
    strictPrime_quotient_dimension p q hpq

end Module
