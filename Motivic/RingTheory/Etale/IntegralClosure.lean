/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Motivic.RingTheory.Etale.GenericFiber
public import Motivic.RingTheory.IntegralClosure.LocalArtinian

/-!
# Relative integral closure for localized étale algebras

A bijective integral-closure comparison transports relative integral closedness
through base change. Smooth comparison followed by arbitrary-localization
comparison applies this to prime localizations of étale algebras over normal
domains. Neither the étale algebra nor its localization is assumed to be a
domain. In particular, the localized algebra is only essentially finite type,
not asserted to be smooth or finitely presented over the original base.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Motivic

/-- A bijective integral-closure comparison transports relative integral
closedness. Its injectivity is part of the conclusion, even for zero divisors. -/
theorem isIntegrallyClosedIn_tensorProduct_of_comparison
    (R : Type u) (S : Type v) (B : Type w)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [IsIntegrallyClosedIn R B]
    (h : Function.Bijective (TensorProduct.toIntegralClosure R S B)) :
    IsIntegrallyClosedIn S (S ⊗[R] B) := by
  let e : S ≃ₐ[S] integralClosure S (S ⊗[R] B) :=
    (Algebra.TensorProduct.rid R S S).symm.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
        (IsIntegralClosure.equiv R R B (integralClosure R B))).trans <|
      AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B) h
  have he (s : S) : (e s : S ⊗[R] B) = algebraMap S (S ⊗[R] B) s := by
    simpa using congrArg Subtype.val (e.commutes s)
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    simpa only [he] using hxy
  · intro x hx
    obtain ⟨s, hs⟩ := e.surjective ⟨x, hx⟩
    exact ⟨s, (he s).symm.trans (congrArg Subtype.val hs)⟩

/-- Smooth base change preserves relative integral closedness, including
injectivity of the resulting map into the tensor product. -/
theorem isIntegrallyClosedIn_tensorProduct_of_smooth
    (R : Type u) (S : Type v) (B : Type w)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [IsIntegrallyClosedIn R B] [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] B) :=
  isIntegrallyClosedIn_tensorProduct_of_comparison R S B
    TensorProduct.toIntegralClosure_bijective_of_smooth

/-- Localizing a smooth algebra preserves relative integral closedness in
its base change. Arbitrary localization uses the tower comparison, so no
finite-presentation hypothesis is imposed on the localized algebra. -/
theorem isIntegrallyClosedIn_tensorProduct_of_smooth_isLocalization
    (R : Type u) (S : Type v) (B : Type w) (C : Type*)
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C]
    [IsScalarTower R S C] [IsIntegrallyClosedIn R B] [Algebra.Smooth R S]
    (M : Submonoid S) [IsLocalization M C] :
    IsIntegrallyClosedIn C (C ⊗[R] B) := by
  apply isIntegrallyClosedIn_tensorProduct_of_comparison R C B
  exact TensorProduct.toIntegralClosure_bijective_of_tower (S := S)
    TensorProduct.toIntegralClosure_bijective_of_smooth
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization M)

/-- A prime localization of an étale algebra over an integrally closed ring
is integrally closed in its scalar extension to the base's total fraction ring. -/
theorem isIntegrallyClosedIn_generic_localizationAtPrime_of_etale
    (R : Type u) (S : Type v) [CommRing R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime] :
    IsIntegrallyClosedIn (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[R] FractionRing R) :=
  isIntegrallyClosedIn_tensorProduct_of_smooth_isLocalization R S (FractionRing R)
    (Localization.AtPrime q) q.primeCompl

/-- Every prime localization of an étale algebra over a normal domain is a
normal domain. The étale algebra itself may be disconnected. -/
theorem normalDomain_localizationAtPrime_of_etale
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  have := isIntegrallyClosedIn_generic_localizationAtPrime_of_etale R S q
  have := isReduced_tensorProduct_fractionRing_of_formallyUnramified R (Localization.AtPrime q)
  have := isArtinianRing_tensorProduct_fractionRing_of_formallyUnramified
    R (Localization.AtPrime q)
  exact normalDomain_of_local_integrallyClosedIn_artinian (Localization.AtPrime q)
    (Localization.AtPrime q ⊗[R] FractionRing R)

end Motivic
