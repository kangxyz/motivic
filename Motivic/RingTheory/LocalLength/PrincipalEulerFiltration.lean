/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Motivic.RingTheory.LocalLength.PrincipalEulerAdditivity
public import Motivic.RingTheory.LocalLength.PrimeFiltration

/-!
# Aglib import adapter for PrincipalEulerFiltration

This temporary downstream adapter preserves the existing Motivic names while
reusing the native Aglib declarations. It adds no mathematical implementation.
The current Aglib revision is recorded in `lake-manifest.json`.
The earlier R5Lab extraction provenance remains in `docs/provenance/early-source-migrations.md`;
the imported Aglib source carries its own Apache-2.0 notices and exact provenance.
-/

@[expose] public section

namespace Motivic.LocalLength

export Module (
  principalEuler_of_quotientFiltration
  principalEuler_add_of_submodule_le
)

end Motivic.LocalLength

namespace Motivic.LocalLength.PrimeFiltrationFrom

export Module.PrimeFiltrationFrom (
  primes
  principalEuler_eq_sum
)

end Motivic.LocalLength.PrimeFiltrationFrom

