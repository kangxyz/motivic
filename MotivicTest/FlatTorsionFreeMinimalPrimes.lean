/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Spectrum.Prime.FlatScalarMinimalPrimes
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Consumers of minimal-prime contraction after flat scalar extension

The ground-field extension has no finite-type or algebraicity assumption.
The original algebra may have several components, have nilpotents, or be zero.
Inseparable support base changes can carry higher fundamental multiplicities;
contraction to zero does not identify a fundamental cycle with its reduction.
-/

@[expose] public section

open scoped TensorProduct

namespace MotivicTest.FlatTorsionFreeMinimalPrimes

variable {K L B : Type*} [Field K] [Field L] [Algebra K L]

/-- No finiteness, reducedness, domain, or flatness hypothesis on this support algebra. -/
theorem arbitraryFieldExtension [CommRing B] [Algebra K B]
    {q : Ideal (L ⊗[K] B)} (hq : q ∈ minimalPrimes (L ⊗[K] B)) :
    q.under L = ⊥ :=
  Ideal.under_eq_bot_of_mem_minimalPrimes_tensorProduct hq

/-- A split support keeps both factors in the actual tensor algebra. -/
theorem disconnectedSupport {q : Ideal (L ⊗[K] (K × K))}
    (hq : q ∈ minimalPrimes (L ⊗[K] (K × K))) : q.under L = ⊥ :=
  arbitraryFieldExtension hq

/-- The square-zero thickening is not reduced, but its minimal primes still dominate. -/
theorem squareZeroSupport {q : Ideal (L ⊗[K] TrivSqZeroExt K K)}
    (hq : q ∈ minimalPrimes (L ⊗[K] TrivSqZeroExt K K)) : q.under L = ⊥ :=
  arbitraryFieldExtension hq

/-- The test support really contains a nonzero nilpotent; no reduction is implicit. -/
theorem squareZeroSupport_has_nonzero_nilpotent :
    ∃ e : TrivSqZeroExt K K, e ≠ 0 ∧ e * e = 0 := by
  refine ⟨TrivSqZeroExt.inr 1, ?_, TrivSqZeroExt.inr_mul_inr _ _ _⟩
  intro h
  have := congrArg TrivSqZeroExt.snd h
  simp at this

/-- The zero support is also permitted; the assertion requires a minimal-prime input. -/
theorem emptySupport {q : Ideal (L ⊗[K] PUnit)}
    (hq : q ∈ minimalPrimes (L ⊗[K] PUnit)) : q.under L = ⊥ :=
  arbitraryFieldExtension hq

/-- A nonzero target scalar cannot vanish in any reduced component. -/
theorem targetScalar_survives [CommRing B] [Algebra K B]
    {q : Ideal (L ⊗[K] B)} (hq : q ∈ minimalPrimes (L ⊗[K] B))
    {s : L} (hs : s ≠ 0) : algebraMap L (L ⊗[K] B) s ∉ q := by
  intro h
  have : s ∈ q.under L := h
  rw [arbitraryFieldExtension hq] at this
  exact hs (Ideal.mem_bot.mp this)

open Lean in
run_cmd do
  for name in #[``Ideal.under_eq_bot_of_mem_minimalPrimes_of_isTorsionFree,
      ``Ideal.under_eq_bot_of_mem_minimalPrimes_tensorProduct,
      ``arbitraryFieldExtension, ``disconnectedSupport, ``squareZeroSupport,
      ``squareZeroSupport_has_nonzero_nilpotent, ``emptySupport, ``targetScalar_survives] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Flat torsion-free minimal-prime contraction uses only standard foundations."

end MotivicTest.FlatTorsionFreeMinimalPrimes
