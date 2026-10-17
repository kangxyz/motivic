/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Motivic.RingTheory.LocalLength.PrimeFiltrationMultiplicity

/-!
# Aglib import adapter for PrincipalEulerAssociativity

This temporary downstream adapter preserves the existing Motivic names while
reusing the native Aglib declarations. It adds no mathematical implementation.
Dependency pin: `kangxyz/aglib` commit `40af743ab794d607f566cec0c5417d8e4d02a735`.
The earlier R5Lab extraction provenance remains in `THIRD_PARTY_NOTICES.md`;
the imported Aglib source carries its own Apache-2.0 notices and exact provenance.
-/

@[expose] public section

namespace Motivic.LocalLength

export Module (
  supportDim_nonpos_of_length_ne_top
  supportDim_le_one_of_finite_cokernel
  support_prime_minimal_or_maximal
  scalar_regular_primeQuotient
  minimalPrimeEulerTerm
  moduleMinimalPrimes
  mem_moduleMinimalPrimes
  principalEuler_associativity
  minimalPrimeCokernelTerm
  minimalPrimeEulerTerm_eq_cokernelTerm
  principalCokernel_associativity
  finitePrincipal_minimalPrime
)

end Motivic.LocalLength

namespace Motivic.LocalLength.PrimeFiltrationFrom

export Module.PrimeFiltrationFrom (
  principalEuler_eq_weighted_sum_of_supportDim
  principalEuler_eq_weighted_sum
)

end Motivic.LocalLength.PrimeFiltrationFrom

