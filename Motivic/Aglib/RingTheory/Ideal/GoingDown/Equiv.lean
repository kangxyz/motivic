/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Transport of going down through compatible ring equivalences

A commuting square with horizontal ring equivalences transports the
going-down property. The proof uses the actual induced homeomorphisms of
prime spectra, so both source and target algebra maps are tracked explicitly.

## Upstream candidate

Intended upstream module: `Aglib.RingTheory.Ideal.GoingDown.Equiv`. The
commutative rings may lie in four independent universes; no domain, finiteness
or flatness premise is added. Current consumers are
`Motivic.Aglib.RingTheory.Ideal.GoingDown.TensorProduct` and
`Motivic.Aglib.RingTheory.Ideal.GoingDown.BaseChange`, which transport the
canonical tensor-quotient and polynomial-tensor equivalences.

Extracted from `Motivic.RingTheory.GoingDown.Equiv`, source SHA-256
`bbb42307a6d334af580be7bfb224009bcb667530f474c99ae39104558cfef9f4`.
The mathematical declarations now extend `Algebra.HasGoingDown`.
-/

@[expose] public section

universe u v w x

namespace Algebra.HasGoingDown

/-- Going down is unchanged by compatible equivalences of both rings. -/
theorem of_equivalences
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra.HasGoingDown R S]
    (e : R ≃+* R') (f : S ≃+* S')
    (h : f.toRingHom.comp (algebraMap R S) = (algebraMap R' S').comp e.toRingHom) :
    Algebra.HasGoingDown R' S' := by
  have hmap : algebraMap R' S' =
      (f.toRingHom.comp (algebraMap R S)).comp e.symm.toRingHom := by
    ext r
    simpa using (congrArg (fun g : R →+* S' => g (e.symm r)) h).symm
  rw [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap, hmap,
    PrimeSpectrum.comap_comp, PrimeSpectrum.comap_comp]
  exact (((PrimeSpectrum.homeomorphOfRingEquiv f).symm.isOpenEmbedding.generalizingMap).comp
    (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance)).comp
      (PrimeSpectrum.homeomorphOfRingEquiv e).isOpenEmbedding.generalizingMap

/-- An algebra equivalence transports going down with its base unchanged. -/
theorem of_algEquiv
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.HasGoingDown R S] (e : S ≃ₐ[R] T) : Algebra.HasGoingDown R T := by
  apply of_equivalences (RingEquiv.refl R) e.toRingEquiv
  ext r
  exact e.commutes r

end Algebra.HasGoingDown
