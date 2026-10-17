/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AlgebraicIndependent.FractionImageTrdeg
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Fraction-field bounds for polynomial coefficient charts

A domain quotient of a polynomial algebra has fraction-field transcendence
degree at most the coefficient domain's transcendence degree plus the number
of variables. The coefficient map to the quotient need not be injective.
The same statement holds after localizing the polynomial algebra away from
any element; nontriviality is recovered from the actual map to the domain.
The finite-coefficient version also allows a possibly non-domain finite algebra
over the coefficient domain, as required after a closed-point base change.
-/

@[expose] public noncomputable section

universe u

namespace Algebra

/-- Adjoining finitely many polynomial parameters adds exactly their number to
the native transcendence degree over the coefficient field. -/
theorem trdeg_mvPolynomial_fintype_eq_add
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] (N : Type) [Fintype N] :
    trdeg k (MvPolynomial N R) = trdeg k R + Fintype.card N := by
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Cardinal.lift_natCast] using (trdeg_add_eq k R (A := MvPolynomial N R)).symm

end Algebra

namespace AlgHom

/-- An actual surjection onto a domain bounds the transcendence degree of its
fraction field. No injectivity of the coefficient map is assumed. -/
theorem trdeg_fractionRing_le_of_surjective
    {k D C K : Type u} [Field k] [CommRing D] [CommRing C] [IsDomain C] [Field K]
    [Algebra k D] [Algebra k C] [Algebra k K] [Algebra C K]
    [IsScalarTower k C K] [IsFractionRing C K]
    (f : D →ₐ[k] C) (hf : Function.Surjective f) :
    Algebra.trdeg k K ≤ Algebra.trdeg k D := by
  apply ((IsScalarTower.toAlgHom k C K).comp f).trdeg_le_of_fractionRing_image_mem
    (C := C)
  intro c
  obtain ⟨d, rfl⟩ := hf c
  exact ⟨d, rfl⟩

/-- A domain quotient of the polynomial coefficient chart contributes at most
one parameter per variable to the fraction field. -/
theorem trdeg_fractionRing_le_of_mvPolynomial_surjective
    {k R C K : Type u} [Field k] [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Field K] [Algebra k R] [Algebra k C] [Algebra k K] [Algebra C K]
    [IsScalarTower k C K] [IsFractionRing C K]
    {N : Type} [Fintype N] (f : MvPolynomial N R →ₐ[k] C) (hf : Function.Surjective f) :
    Algebra.trdeg k K ≤ Algebra.trdeg k R + Fintype.card N := by
  simpa only [Algebra.trdeg_mvPolynomial_fintype_eq_add] using
    f.trdeg_fractionRing_le_of_surjective (K := K) hf

/-- Localizing the actual polynomial chart introduces no extra parameter.
Existence of the map to the domain rules out the zero localization, so no
nonzero-denominator or coefficient-injectivity premise is necessary. -/
theorem trdeg_fractionRing_le_of_localized_mvPolynomial_surjective
    {k R C K : Type u} [Field k] [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Field K] [Algebra k R] [Algebra k C] [Algebra k K] [Algebra C K]
    [IsScalarTower k C K] [IsFractionRing C K]
    {N : Type} [Fintype N] (r : MvPolynomial N R)
    (f : Localization.Away r →ₐ[k] C) (hf : Function.Surjective f) :
    Algebra.trdeg k K ≤ Algebra.trdeg k R + Fintype.card N := by
  let D := MvPolynomial N R
  let L := Localization.Away r
  have : Nontrivial L := f.toRingHom.domain_nontrivial
  have hr : r ≠ 0 := by
    intro h
    have hu := IsLocalization.Away.algebraMap_isUnit (S := L) r
    exact hu.ne_zero ((congrArg (algebraMap D L) h).trans (map_zero _))
  have : IsDomain L := Localization.Away.isDomain hr
  have : FaithfulSMul D L :=
    (faithfulSMul_iff_algebraMap_injective D L).mpr
      (IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hr))
  have : Algebra.IsAlgebraic D L :=
    IsLocalization.isAlgebraic L (Submonoid.powers r)
  have hdeg : Algebra.trdeg k L = Algebra.trdeg k D := by
    simpa only [trdeg_eq_zero, add_zero] using
      (trdeg_add_eq k D (A := L)).symm
  exact (f.trdeg_fractionRing_le_of_surjective (K := K) hf).trans_eq
    (hdeg.trans (Algebra.trdeg_mvPolynomial_fintype_eq_add k R N))

/-- Integral coefficients, localization, taking a domain quotient, and passing
to its fraction field do not increase transcendence degree. The integral
algebra and its localization need not be domains, and the base map may have
kernel. The proof uses the actual image of the base in the fraction field.
The domain hypothesis stays explicit for callers working with domain quotients. -/
@[nolint unusedArguments]
theorem trdeg_fractionRing_le_of_integral_localization_surjective
    {k D A C K : Type u} [Field k] [CommRing D] [CommRing A] [CommRing C]
    [IsDomain C] [Field K] [Algebra k D] [Algebra k A] [Algebra D A]
    [IsScalarTower k D A] [Algebra.IsIntegral D A]
    [Algebra k C] [Algebra k K] [Algebra C K]
    [IsScalarTower k C K] [IsFractionRing C K]
    (r : A) (f : Localization.Away r →ₐ[k] C) (hf : Function.Surjective f) :
    Algebra.trdeg k K ≤ Algebra.trdeg k D := by
  let L := Localization.Away r
  let q : L →ₐ[k] K := (IsScalarTower.toAlgHom k C K).comp f
  let g : A →ₐ[k] K := q.comp (IsScalarTower.toAlgHom k A L)
  let b : D →ₐ[k] K := g.comp (IsScalarTower.toAlgHom k D A)
  let S := b.range
  have hA : ∀ a : A, IsAlgebraic S (g a) := by
    intro a
    exact (IsIntegral.map_of_comp_eq b.rangeRestrict.toRingHom g.toRingHom
      (by ext x; rfl) (Algebra.IsIntegral.isIntegral a)).isAlgebraic
  have hL : ∀ l : L, IsAlgebraic S (q l) := by
    intro l
    obtain ⟨⟨a, m⟩, h⟩ := IsLocalization.surj (Submonoid.powers r) l
    have hm : g m ≠ 0 := ((IsLocalization.map_units L m).map q.toRingHom).ne_zero
    have he : q l * g m = g a := by
      change q l * q (algebraMap A L m) = q (algebraMap A L a)
      exact (map_mul q l (algebraMap A L m)).symm.trans (congrArg q h)
    rw [(eq_div_iff hm).mpr he, div_eq_mul_inv]
    exact (hA a).mul (hA m).inv
  have hC : ∀ c : C, IsAlgebraic S (algebraMap C K c) := by
    intro c
    obtain ⟨l, rfl⟩ := hf c
    exact hL l
  have : Algebra.IsAlgebraic S K := ⟨fun z => by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective C z
    rw [div_eq_mul_inv]
    exact (hC x).mul (hC y).inv⟩
  have hdeg : Algebra.trdeg k K = Algebra.trdeg k S := by
    simpa only [trdeg_eq_zero, add_zero] using (trdeg_add_eq k S (A := K)).symm
  exact hdeg.le.trans (trdeg_le_of_surjective b.rangeRestrict b.rangeRestrict_surjective)

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Finite coefficient algebras contribute no additional parameters, even if
they have nilpotents or several components. Only the final quotient is a domain. -/
theorem trdeg_fractionRing_le_of_finite_localized_mvPolynomial_surjective
    {k R B C K : Type u} [Field k] [CommRing R] [IsDomain R] [CommRing B]
    [CommRing C] [IsDomain C] [Field K]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Module.Finite R B]
    [Algebra k C] [Algebra k K] [Algebra C K]
    [IsScalarTower k C K] [IsFractionRing C K]
    {N : Type} [Fintype N] (r : MvPolynomial N B)
    (f : Localization.Away r →ₐ[k] C) (hf : Function.Surjective f) :
    Algebra.trdeg k K ≤ Algebra.trdeg k R + Fintype.card N := by
  have : IsScalarTower k R (MvPolynomial N B) :=
    IsScalarTower.to₁₂₄ k R B (MvPolynomial N B)
  have : IsScalarTower k (MvPolynomial N R) (MvPolynomial N B) :=
    IsScalarTower.to₁₃₄ k R (MvPolynomial N R) (MvPolynomial N B)
  have : Algebra.IsIntegral (MvPolynomial N R) (MvPolynomial N B) := ⟨fun p =>
    MvPolynomial.isIntegral_iff_isIntegral_coeff.mpr fun _ => IsIntegral.of_finite R _⟩
  exact (f.trdeg_fractionRing_le_of_integral_localization_surjective
    (D := MvPolynomial N R) (K := K) r hf).trans_eq
      (Algebra.trdeg_mvPolynomial_fintype_eq_add k R N)

end AlgHom

namespace Ideal

/-- The fraction field of an actual prime polynomial quotient satisfies the
coefficient-chart bound, without any disjointness condition on the prime. -/
theorem trdeg_fractionRing_mvPolynomial_quotient_le
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {N : Type} [Fintype N] (P : Ideal (MvPolynomial N R)) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (MvPolynomial N R ⧸ P)) ≤
      Algebra.trdeg k R + Fintype.card N :=
  (Ideal.Quotient.mkₐ k P).trdeg_fractionRing_le_of_mvPolynomial_surjective
    (Ideal.Quotient.mkₐ_surjective k P)

/-- The corresponding actual prime quotient of a principal localization. -/
theorem trdeg_fractionRing_localized_mvPolynomial_quotient_le
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {N : Type} [Fintype N] (r : MvPolynomial N R) (P : Ideal (Localization.Away r)) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (Localization.Away r ⧸ P)) ≤
      Algebra.trdeg k R + Fintype.card N :=
  (Ideal.Quotient.mkₐ k P).trdeg_fractionRing_le_of_localized_mvPolynomial_surjective r
    (Ideal.Quotient.mkₐ_surjective k P)

/-- The coefficient-chart bound for a prime quotient with a finite coefficient
algebra; reducedness or geometric integrality of that algebra is not required. -/
theorem trdeg_fractionRing_finite_localized_mvPolynomial_quotient_le
    {k R B : Type u} [Field k] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Module.Finite R B]
    {N : Type} [Fintype N] (r : MvPolynomial N B)
    (P : Ideal (Localization.Away r)) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (Localization.Away r ⧸ P)) ≤
      Algebra.trdeg k R + Fintype.card N :=
  (Ideal.Quotient.mkₐ k P).trdeg_fractionRing_le_of_finite_localized_mvPolynomial_surjective
    (R := R) r (Ideal.Quotient.mkₐ_surjective k P)

end Ideal
