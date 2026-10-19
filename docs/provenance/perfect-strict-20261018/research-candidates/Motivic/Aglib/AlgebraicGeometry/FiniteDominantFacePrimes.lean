/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.MinimalPrimeGoingDown
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Original face primes of a finite dominant integral support

Going down identifies the contraction of every minimal prime over the literal
extended face ideal. The geometric consumer derives the integral injective
coordinate map from the actual finite dominant scheme morphism. Normality of
the affine base, not flatness of the support, supplies going down. This records
only support genericity over the face; local dimensions and endpoint lengths
remain separate. No scheme-theoretic multiplicities are discarded.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

universe u v

namespace Ideal

/-- Under an integral injective map from a normal domain, a minimal prime over
an extended prime ideal contracts to that exact original prime. -/
theorem comap_eq_of_mem_minimalPrimes_map_prime
    {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] (φ : R →+* S) (hφ : Function.Injective φ)
    (hfinite : φ.Finite) (I : Ideal R) [I.IsPrime] (Q : Ideal S)
    (hQ : Q ∈ (I.map φ).minimalPrimes) : Q.comap φ = I := by
  let : Algebra R S := φ.toAlgebra
  have : Module.Finite R S := hfinite
  have : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr hφ
  have h := under_mem_minimalPrimes_of_hasGoingDown I Q hQ
  rw [minimalPrimes_eq_subsingleton_self] at h
  exact h

end Ideal

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {D : Scheme.{u}} [IsIntegral D]
  (f : D ⟶ Spec (.of A[X])) [IsFinite f] [IsDominant f]

/-- The original global coordinate map, with the canonical Spec comparison. -/
def coordinateMap : A[X] →+* Γ(D, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of A[X])).inv.hom

omit [IsDomain A] [IsIntegrallyClosed A] [IsIntegral D] [IsDominant f] in
private theorem coordinateMap_finite : (coordinateMap f).Finite := by
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (.of A[X])).commRingCatIsoToRingEquiv.symm.surjective)

omit [IsIntegrallyClosed A] [IsIntegral D] in
private theorem coordinateMap_injective : Function.Injective (coordinateMap f) := by
  let : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  have hf : Function.Injective f.appTop := by
    rw [RingHom.injective_iff_ker_eq_bot,
      ← f.ker_apply ⟨⊤, isAffineOpen_top _⟩, f.ker_eq_bot]
    simp
  exact hf.comp (Scheme.ΓSpecIso (.of A[X])).commRingCatIsoToRingEquiv.symm.injective

/-- Every original irreducible face component maps to the generic face prime.
The ideal is the full extended principal ideal, not a chosen reduced replacement. -/
theorem face_minimalPrime_comap (a : A) (Q : Ideal Γ(D, ⊤))
    (hQ : Q ∈ ((Ideal.span {Polynomial.X - Polynomial.C a}).map
      (coordinateMap f)).minimalPrimes) :
    Q.comap (coordinateMap f) = Ideal.span {Polynomial.X - Polynomial.C a} := by
  have : (Ideal.span {Polynomial.X - Polynomial.C a} : Ideal A[X]).IsPrime := by
    rw [← Polynomial.ker_evalRingHom]
    exact RingHom.ker_isPrime (Polynomial.evalRingHom a)
  exact Ideal.comap_eq_of_mem_minimalPrimes_map_prime (coordinateMap f)
    (coordinateMap_injective f) (coordinateMap_finite f) _ Q hQ

end AlgebraicGeometry.Scheme.FiniteDominantFace
