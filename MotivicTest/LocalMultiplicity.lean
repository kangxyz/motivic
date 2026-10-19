/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.RingTheory.LocalLength.KoszulPairMultiplicity

/-!
# Local multiplicity consumers

These tests use the actual higher homology modules, coordinate swap and
weighted principal formula. The zero pair checks that the Euler expression
retains higher-homology corrections; it is not a proper-intersection example.
-/

open Module Module.KoszulPair

universe u v

namespace MotivicTest.LocalMultiplicity

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

example (a b : R) (h : HasFiniteHomology M a b) :
    eulerMultiplicity M a b h =
      eulerMultiplicity M b a ((hasFiniteHomology_swap M a b).mp h) :=
  eulerMultiplicity_swap M a b h

example (a b : R) [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (ha : IsSMulRegular M a) (hb : IsSMulRegular (PrincipalQuotient M a) b)
    (hbm : b ∈ IsLocalRing.maximalIdeal R) (h : HasFiniteHomology M a b) :
    eulerMultiplicity M a b h =
      ∑ p ∈ moduleMinimalPrimes (A := R) (PrincipalQuotient M a),
        minimalPrimeCokernelTerm (PrincipalQuotient M a) b p :=
  eulerMultiplicity_eq_weighted_principal M a b ha hb hbm h

/-- Even when H₀ is nonzero, the higher corrections can cancel its whole length. -/
example (h : HasFiniteHomology M (0 : R) 0) :
    eulerMultiplicity M (0 : R) 0 h = 0 := by
  have hr : LinearMap.range (d₁ M (0 : R) 0) = ⊥ := by simp [d₁]
  have hk : Cycles M (0 : R) 0 = ⊤ := by simp [Cycles, d₁]
  have hd : toCycles M (0 : R) 0 = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [toCycles, d₂]
  let e₀ : H₀ M (0 : R) 0 ≃ₗ[R] M := Submodule.quotEquivOfEqBot _ hr
  let e₁ : H₁ M (0 : R) 0 ≃ₗ[R] M × M :=
    (Submodule.quotEquivOfEqBot _ (by rw [hd, LinearMap.range_zero])).trans
      ((LinearEquiv.ofEq _ _ hk).trans (Submodule.topEquiv (R := R) (M := M × M)))
  let e₂ : H₂ M (0 : R) 0 ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ (show LinearMap.ker (d₂ M (0 : R) 0) = ⊤ by
      simp [d₂])).trans (Submodule.topEquiv (R := R) (M := M))
  have hM : Module.length R M ≠ ⊤ := by
    rw [← e₀.length_eq]
    exact h.1
  simp only [eulerMultiplicity, e₀.length_eq, e₁.length_eq, e₂.length_eq,
    Module.length_prod, ENat.toNat_add hM hM, Nat.cast_add]
  omega

end MotivicTest.LocalMultiplicity
