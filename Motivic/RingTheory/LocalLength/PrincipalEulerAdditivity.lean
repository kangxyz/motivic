/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.ScalarHomology.Basic
public import Motivic.RingTheory.LocalLength.PrincipalEuler

/-!
# Aglib import adapter for PrincipalEulerAdditivity

This temporary downstream adapter preserves the existing Motivic names while
reusing the native Aglib declarations. It adds no mathematical implementation.
The current Aglib revision is recorded in `lake-manifest.json`.
The earlier R5Lab extraction provenance remains in `docs/provenance/early-source-migrations.md`;
the imported Aglib source carries its own Apache-2.0 notices and exact provenance.
-/

@[expose] public section

namespace Motivic.LocalLength

export Module (
  ScalarKernel
  ScalarCokernel
  scalarKernelMap
  scalarKernelMap_apply
  scalarCokernelMap
  scalarCokernelMap_mk
  scalarKernelMap_injective
  scalarKernelMap_exact
  scalarCokernelMap_surjective
  scalarCokernelMap_exact
  scalarSquare
  principalConnecting
  principalConnecting_exact_right
  principalConnecting_exact_left
  intLength
  intLength_add_of_exact
  intLength_exact_pair
  FinitePrincipal
  finitePrincipal_of_regular
  principalEuler_add_of_exact
  scalarKernelEquiv
  scalarCokernelEquiv
  principalEuler_congr
  finitePrincipal_congr
)

end Motivic.LocalLength

namespace Motivic.LocalLength

export Int (
  integer_telescope
)

end Motivic.LocalLength

