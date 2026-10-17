module

public import Motivic.Aglib.RingTheory.AlgebraicIndependent.FractionImageTrdeg
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Fraction-field bounds for polynomial coefficient charts

A domain quotient of a polynomial algebra has fraction-field transcendence
degree at most the coefficient domain's transcendence degree plus the number
of variables. The coefficient map to the quotient need not be injective.
The same statement holds after localizing the polynomial algebra away from
any element; nontriviality is recovered from the actual map to the domain.
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
    rw [h, map_zero] at hu
    exact not_isUnit_zero hu
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

end Ideal
