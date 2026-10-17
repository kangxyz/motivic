/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.FiniteHomologyExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Actual product and split-complex consumers of finite homology exactness -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Motivic.LengthEuler

universe u v w

namespace MotivicTest.FiniteHomologyExact

variable {R : Type u} [Ring R]

/-- Degreewise actual product modules inherit finite-length support. -/
theorem productSupport {ι : Type w} (X Z : ι → ModuleCat.{v} R)
    (hX : FiniteLengthSupport X) (hZ : FiniteLengthSupport Z) :
    FiniteLengthSupport (fun i => ModuleCat.of R (X i × Z i)) :=
  FiniteLengthSupport.of_exact
    (fun _ => ModuleCat.ofHom (LinearMap.inl R _ _))
    (fun _ => ModuleCat.ofHom (LinearMap.snd R _ _))
    (fun _ => Function.Exact.inl_snd) hX hZ

variable (K L : ChainComplex (ModuleCat.{v} R) ℕ)

/-- Actual binary biproducts of complexes preserve finite homology. -/
theorem biproductFinite (hK : FiniteHomology K) (hL : FiniteHomology L) :
    FiniteHomology (K ⊞ L) :=
  FiniteHomology.shortExact_middle _
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hK hL

/-- The left summand is recovered from the actual split sequence. -/
theorem leftSummandFinite (hKL : FiniteHomology (K ⊞ L)) (hL : FiniteHomology L) :
    FiniteHomology K :=
  FiniteHomology.shortExact_left _
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hKL hL

/-- The right summand recovery includes the degree-zero homology quotient. -/
theorem rightSummandFinite (hK : FiniteHomology K) (hKL : FiniteHomology (K ⊞ L)) :
    FiniteHomology L :=
  FiniteHomology.shortExact_right _
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hK hKL

/-- Euler length of the actual biproduct is the sum without an assumed middle witness. -/
theorem biproductEuler (hK : FiniteHomology K) (hL : FiniteHomology L) :
    chainEuler (K ⊞ L) (biproductFinite K L hK hL) =
      chainEuler K hK + chainEuler L hL :=
  chainEuler_add_of_shortExact_outer _
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hK hL

end MotivicTest.FiniteHomologyExact
