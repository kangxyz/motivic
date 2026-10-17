/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.KoszulPairFiniteLength

/-!
# Finite-length consumers without regularity hypotheses

The first tests exercise annihilation over arbitrary commutative rings. The
last test derives all finite homology lengths from the Artinian ideal quotient.
-/

@[expose] public section

universe u v

open Motivic.LocalLength.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

example : Ideal.span ({a, b} : Set R) ≤ Module.annihilator R (H₁ M a b) :=
  span_le_annihilator_H₁ M a b

example (z : H₂ M a b) : a • z = 0 :=
  Module.mem_annihilator.mp (first_mem_annihilator_H₂ M a b) z

example [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))] : HasFiniteHomology M a b :=
  hasFiniteHomology_of_artinian_quotient M a b
