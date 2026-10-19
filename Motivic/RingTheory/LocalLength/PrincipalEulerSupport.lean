/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Support
public import Motivic.RingTheory.LocalLength.PrincipalEulerFiltration

/-!
# Aglib import adapter for PrincipalEulerSupport

This temporary downstream adapter preserves the existing Motivic names while
reusing the native Aglib declarations. It adds no mathematical implementation.
The current Aglib revision is recorded in `lake-manifest.json`.
The earlier R5Lab extraction provenance remains in `docs/provenance/early-source-migrations.md`;
the imported Aglib source carries its own Apache-2.0 notices and exact provenance.
-/

@[expose] public section

namespace Motivic.LocalLength

export Module (
  isMaximal_of_mem_support_of_length_ne_top
  length_add_of_submodule_le
  length_ne_top_of_support_isMaximal
  support_scalarCokernel
  scalar_mem_annihilator_kernel
  scalar_mem_annihilator_cokernel
  finitePrincipal_of_support_subset
)

end Motivic.LocalLength

namespace Motivic.LocalLength.PrimeFiltrationFrom

export Module.PrimeFiltrationFrom (
  primes_isPrime
  prime_mem_support
  length_eq_add_sum
  primeFactor_support_subset
  finitePrincipal_terms
  principalEuler_eq_sum_of_finite_cokernel
)

end Motivic.LocalLength.PrimeFiltrationFrom

