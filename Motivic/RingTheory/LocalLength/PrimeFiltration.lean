/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PrimeFiltration.Basic

/-!
# Aglib import adapter for PrimeFiltration

This temporary downstream adapter preserves the existing Motivic names while
reusing the native Aglib declarations. It adds no mathematical implementation.
The current Aglib revision is recorded in `lake-manifest.json`.
The earlier R5Lab extraction provenance remains in `docs/provenance/early-source-migrations.md`;
the imported Aglib source carries its own Apache-2.0 notices and exact provenance.
-/

@[expose] public section

namespace Motivic.LocalLength

export Module (
  exists_prime_cyclic_submodule
  PrimeFiltrationFrom
  nonempty_primeFiltrationFrom
  nonempty_primeFiltration
)

end Motivic.LocalLength

namespace Motivic.LocalLength

export Submodule (
  comapMkQQuotientEquiv
)

end Motivic.LocalLength

