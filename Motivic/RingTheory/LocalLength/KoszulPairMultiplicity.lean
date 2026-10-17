/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.KoszulPairSymmetry
public import Motivic.RingTheory.LocalLength.KoszulPairQuotient
public import Motivic.RingTheory.LocalLength.PrincipalEulerAssociativity

/-!
# Weighted local multiplicity for a regular pair

The actual two-equation Koszul Euler multiplicity is computed by the minimal
support primes after the first quotient. The weights are localized lengths of
that actual quotient, rather than arbitrary multiplicity inputs. This is an
exact consumer of the extracted prime-filtration/principal-Euler construction.

Only this local regular-pair scope is proved. Arbitrary smooth finite
correspondences still require general Tor multiplicities, geometric support
control, pushforward and the projection formula.
-/

@[expose] public section

universe u v

namespace Motivic.LocalLength.KoszulPair

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (a b : R)

/-- Two-equation regular intersection multiplicity, expanded over the actual
minimal primes of the first quotient with its actual local-length weights. -/
theorem eulerMultiplicity_eq_weighted_principal (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b)
    (hbm : b ∈ IsLocalRing.maximalIdeal R) (h : HasFiniteHomology M a b) :
    eulerMultiplicity M a b h =
      ∑ p ∈ moduleMinimalPrimes (A := R) (PrincipalQuotient M a),
        minimalPrimeCokernelTerm (PrincipalQuotient M a) b p := by
  rw [eulerMultiplicity_of_regular M a b ha hb h,
    ← (iteratedQuotientEquiv M a b).length_eq]
  exact principalCokernel_associativity b hbm hb (by
    change Module.length R (PrincipalQuotient (PrincipalQuotient M a) b) ≠ ⊤
    rw [(iteratedQuotientEquiv M a b).length_eq]
    exact h.1)

end Motivic.LocalLength.KoszulPair
