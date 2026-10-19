/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.IntegralClosure
public import Motivic.Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Normal local rings of smooth algebras over normal domains

Standard-étale polynomial charts, polynomial normality, and normality of prime
localizations of étale algebras prove actual domain and integral-closedness
statements for every prime localization of a smooth algebra over any normal
domain. The smooth algebra is not assumed to be a domain or nontrivial.
The field-base wrappers apply to every field, with no perfectness hypothesis.
-/

@[expose] public section

universe u v

namespace Algebra.Smooth
open _root_.Algebra.Etale

/-- Every prime localization of a smooth algebra over a normal domain is a
normal domain. Neither global irreducibility nor Noetherianity is assumed. -/
theorem normalDomain_localizationAtPrime_of_smooth
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (q : Ideal A) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨f, hf, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := q)
  have := MvPolynomial.isIntegrallyClosed_fin (R := R) n
  let p := q.map (algebraMap A (Localization.Away f))
  have hd : Disjoint (Submonoid.powers f : Set A) (q : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  have : p.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) q
      inferInstance hd
  have hp : p.comap (algebraMap A (Localization.Away f)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) (Localization.Away f)
      inferInstance hd
  have : IsLocalization.AtPrime (Localization.AtPrime p) q := by
    simpa only [hp] using
      (inferInstance : IsLocalization.AtPrime (Localization.AtPrime p)
        (p.comap (algebraMap A (Localization.Away f))))
  obtain ⟨hdom, hnormal⟩ := normalDomain_localizationAtPrime_of_etale
    (MvPolynomial (Fin n) R) (Localization.Away f) p
  let e : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

/-- Every prime localization of a smooth algebra over a field is a normal
domain. Disconnected smooth algebras and imperfect fields are allowed. -/
theorem normalDomain_localizationAtPrime_of_smooth_field
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  normalDomain_localizationAtPrime_of_smooth k A q

/-- A domain smooth over a normal domain is integrally closed. -/
theorem isIntegrallyClosed_of_smooth
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] [IsDomain A] :
    IsIntegrallyClosed A := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro q _ _
  exact (normalDomain_localizationAtPrime_of_smooth R A q).2

/-- A smooth algebra over a field that is a domain is integrally closed.
The domain assumption is needed only for this global consumer. -/
theorem isIntegrallyClosed_of_smooth_field
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] [IsDomain A] : IsIntegrallyClosed A :=
  isIntegrallyClosed_of_smooth k A

end Algebra.Smooth
