/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Motivic.RingTheory.LocalLength.PrincipalEulerSupport

/-!
# Aglib import adapter for PrimeFiltrationMultiplicity

This temporary downstream adapter preserves the existing Motivic names while
reusing the native Aglib declarations. It adds no mathematical implementation.
Dependency pin: `kangxyz/aglib` commit `40af743ab794d607f566cec0c5417d8e4d02a735`.
The earlier R5Lab extraction provenance remains in `THIRD_PARTY_NOTICES.md`;
the imported Aglib source carries its own Apache-2.0 notices and exact provenance.
-/

@[expose] public section

namespace Motivic.LocalLength

export Module (
  length_baseChange_add_of_submodule_le
  localized_primeQuotient_length
)

end Motivic.LocalLength

namespace Motivic.LocalLength.PrimeFiltrationFrom

export Module.PrimeFiltrationFrom (
  length_baseChange_eq_add_sum
  localized_length_eq_count
  localized_length_eq_count_of_bot
  exists_prime_le_of_mem_support
  minimalPrime_mem_primes
)

end Motivic.LocalLength.PrimeFiltrationFrom

