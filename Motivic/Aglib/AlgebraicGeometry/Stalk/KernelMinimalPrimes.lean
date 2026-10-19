/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Points
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Actual ambient-stalk minimal primes and global support components

Minimal primes over the kernel of a surjective actual ambient-to-support
stalk map correspond to genuine global support generic points specializing
to the chosen support point. Both the ring-ideal map and the scheme point
map are literal. No dimension, reducedness or Noetherian assumption enters.
A separately chosen equation ideal must still be proved equal to this kernel
before applying the correspondence to a Koszul replacement formula.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A literal affine-spectrum point is generic exactly when its ideal is a
minimal prime of the original ring, without passing to a reduction. -/
theorem spec_mem_genericPoints_iff_minimalPrime (R : Type u) [CommRing R]
    (p : PrimeSpectrum R) :
    p ∈ genericPoints (Spec (.of R)) ↔ p.asIdeal ∈ minimalPrimes R := by
  change closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) ↔ _
  simpa only [PrimeSpectrum.vanishingIdeal_singleton] using
    (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes (s := ({p} : Set (PrimeSpectrum R)))).symm

/-- The actual affine generic-point/minimal-prime equivalence keeps the same ideal. -/
def specGenericMinimalPrimeEquiv (R : Type u) [CommRing R] :
    genericPoints (Spec (.of R)) ≃ minimalPrimes R where
  toFun p := ⟨p.1.asIdeal, (spec_mem_genericPoints_iff_minimalPrime R p.1).mp p.2⟩
  invFun p := ⟨⟨p.1, p.2.isPrime⟩,
    (spec_mem_genericPoints_iff_minimalPrime R ⟨p.1, p.2.isPrime⟩).mpr p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Contraction through an actual surjection sends minimal primes precisely
to minimal primes over its actual kernel. -/
def kernelMinimalPrimeMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : minimalPrimes S) :
    (RingHom.ker f).minimalPrimes :=
  ⟨p.1.comap f, by
    simpa only [RingHom.ker_eq_comap_bot] using
      (Ideal.minimalPrimes_comap_of_surjective hf p.2)⟩

/-- The literal ideal contraction on minimal primes is bijective. -/
theorem kernelMinimalPrimeMap_bijective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Function.Bijective (kernelMinimalPrimeMap f hf) := by
  constructor
  · intro p q h
    apply Subtype.ext
    exact Ideal.comap_injective_of_surjective f hf (congrArg Subtype.val h)
  · intro p
    have hp : p.1 ∈ Ideal.comap f '' minimalPrimes S := by
      rw [← Ideal.comap_minimalPrimes_eq_of_surjective hf,
        ← RingHom.ker_eq_comap_bot]
      exact p.2
    obtain ⟨q, hq, heq⟩ := hp
    exact ⟨⟨q, hq⟩, Subtype.ext heq⟩

/-- Minimal primes over a surjection kernel are exactly the contractions of
minimal primes of its unreduced target ring. -/
noncomputable def kernelMinimalPrimeEquiv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    minimalPrimes S ≃ (RingHom.ker f).minimalPrimes :=
  Equiv.ofBijective (kernelMinimalPrimeMap f hf) (kernelMinimalPrimeMap_bijective f hf)

/-- The genuine ambient-stalk kernel indexes exactly the global support
components whose closures contain the chosen point. -/
noncomputable def stalkKernelGenericEquiv {Z T : Scheme.{u}} (i : Z ⟶ T)
    [SurjectiveOnStalks i] (z : Z) :
    (RingHom.ker (i.stalkMap z).hom).minimalPrimes ≃
      {y : genericPoints Z // y.1 ⤳ z} :=
  (kernelMinimalPrimeEquiv (i.stalkMap z).hom (i.stalkMap_surjective z)).symm |>.trans
    ((specGenericMinimalPrimeEquiv (Z.presheaf.stalk z)).symm.trans
      (stalkGenericPointEquiv Z z))

/-- The reverse map is the literal contraction through the actual stalk map
of the prime picked by the actual stalk-spectrum generic-point equivalence. -/
theorem stalkKernelGenericEquiv_symm_val {Z T : Scheme.{u}} (i : Z ⟶ T)
    [SurjectiveOnStalks i] (z : Z) (y : {y : genericPoints Z // y.1 ⤳ z}) :
    ((stalkKernelGenericEquiv i z).symm y).1 =
      (((stalkGenericPointEquiv Z z).symm y).1.asIdeal).comap (i.stalkMap z).hom := rfl

end AlgebraicGeometry.Scheme
