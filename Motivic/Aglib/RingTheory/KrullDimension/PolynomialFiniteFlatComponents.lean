/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Spectrum.Prime.FlatScalarMinimalPrimes
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.PID

/-!
# Component dimension of finite flat affine-line covers

Every irreducible component of the spectrum of a finite flat algebra over a
polynomial ring over a field has dimension one. More generally, integrality
and torsion-freeness over the polynomial ring suffice.

The source algebra is the actual algebra, with no reducedness, connectedness,
nontriviality, or positive-rank assumption. In particular the zero algebra is
allowed: the component-wise conclusion is then vacuous.

This is the affine supplier for the separate finite-flat projective-line
component-dimension bridge, which uses the actual two polynomial charts.

Intended upstream module: `Aglib.RingTheory.KrullDimension.PolynomialFiniteFlatComponents`.
Current direct import consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Dimension.FiniteFlatComponents`.
The interfaces and exact hypotheses are given in the declarations below.
-/

@[expose] public section

open Topology

/-- Integral extensions do not increase Krull dimension, without any injectivity
or nontriviality hypothesis on the structural map. -/
theorem ringKrullDim_le_of_isIntegral (R A : Type*)
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under (R := R) hpq

namespace Ideal

/-- A minimal prime of an integral torsion-free polynomial algebra has a strict
prime specialization. The proof lifts the prime kernel of constant coefficient. -/
theorem exists_prime_gt_of_mem_minimalPrimes_polynomial
    {K A : Type*} [Field K] [CommRing A] [Algebra (Polynomial K) A]
    [Algebra.IsIntegral (Polynomial K) A] [Module.IsTorsionFree (Polynomial K) A]
    {q : Ideal A} (hq : q ∈ minimalPrimes A) :
    ∃ Q : Ideal A, q < Q ∧ Q.IsPrime := by
  let p : Ideal (Polynomial K) := RingHom.ker Polynomial.constantCoeff
  let : p.IsPrime := RingHom.ker_isPrime Polynomial.constantCoeff
  let : q.IsPrime := hq.1.1
  let : q.LiesOver (⊥ : Ideal (Polynomial K)) :=
    ⟨(under_eq_bot_of_mem_minimalPrimes_of_isTorsionFree (R := Polynomial K) hq).symm⟩
  have hbot : (⊥ : Ideal (Polynomial K)) < p := by
    refine bot_lt_iff_ne_bot.mpr ?_
    intro hp
    have hX : (Polynomial.X : Polynomial K) ∈ p := by
      simp [p]
    rw [hp, Ideal.mem_bot] at hX
    exact Polynomial.X_ne_zero hX
  obtain ⟨Q, hqQ, hQ, _⟩ :=
    exists_ideal_gt_liesOver_of_lt (p := ⊥) (q := p) q hbot
  exact ⟨Q, hqQ, hQ⟩

/-- The quotient by any minimal prime of an integral torsion-free polynomial
algebra over a field has Krull dimension one. -/
theorem ringKrullDim_quotient_eq_one_of_mem_minimalPrimes_polynomial
    {K A : Type*} [Field K] [CommRing A] [Algebra (Polynomial K) A]
    [Algebra.IsIntegral (Polynomial K) A] [Module.IsTorsionFree (Polynomial K) A]
    {q : Ideal A} (hq : q ∈ minimalPrimes A) :
    ringKrullDim (A ⧸ q) = 1 := by
  refine le_antisymm ?_ ?_
  · refine (ringKrullDim_quotient_le q).trans
      ((ringKrullDim_le_of_isIntegral (Polynomial K) A).trans ?_)
    exact (Ring.krullDimLE_iff (R := Polynomial K) (n := 1)).mp inferInstance
  · rw [ringKrullDim_quotient]
    obtain ⟨Q, hqQ, hQ⟩ := exists_prime_gt_of_mem_minimalPrimes_polynomial (K := K) hq
    have hqmem : (⟨q, hq.1.1⟩ : PrimeSpectrum A) ∈
        PrimeSpectrum.zeroLocus (q : Set A) :=
      (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun _ hx ↦ hx)
    have hQmem : (⟨Q, hQ⟩ : PrimeSpectrum A) ∈
        PrimeSpectrum.zeroLocus (q : Set A) :=
      (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun _ hx ↦ hqQ.le hx)
    exact Order.one_le_krullDim_iff.mpr
      ⟨⟨⟨q, hq.1.1⟩, hqmem⟩, ⟨⟨Q, hQ⟩, hQmem⟩, hqQ⟩

end Ideal

namespace PrimeSpectrum

/-- The topological dimension of an ideal's zero locus is the ring dimension
of the actual quotient, including nilpotent and zero quotients. -/
theorem topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient
    {A : Type*} [CommRing A] (q : Ideal A) :
    topologicalKrullDim (zeroLocus (q : Set A)) = ringKrullDim (A ⧸ q) := by
  let e := q.primeSpectrumQuotientOrderIsoZeroLocus.toEquiv
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp
    (comap_isInducing_of_surjective (A ⧸ q) (Ideal.Quotient.mk q)
      Ideal.Quotient.mk_surjective)
  let h := e.toHomeomorphOfIsInducing he
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (IsHomeomorph.topologicalKrullDim_eq h h.isHomeomorph).symm

/-- Every irreducible component of the spectrum of an integral torsion-free
algebra over a polynomial ring over a field has dimension one. -/
theorem topologicalKrullDim_eq_one_of_mem_irreducibleComponents_polynomial
    {K A : Type*} [Field K] [CommRing A] [Algebra (Polynomial K) A]
    [Algebra.IsIntegral (Polynomial K) A] [Module.IsTorsionFree (Polynomial K) A]
    {Z : Set (PrimeSpectrum A)} (hZ : Z ∈ irreducibleComponents (PrimeSpectrum A)) :
    topologicalKrullDim Z = 1 := by
  rw [← zeroLocus_minimalPrimes] at hZ
  obtain ⟨q, hq, rfl⟩ := hZ
  exact (topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient q).trans
    (Ideal.ringKrullDim_quotient_eq_one_of_mem_minimalPrimes_polynomial (K := K) hq)

/-- Finite flat affine-line algebras have one-dimensional irreducible components;
no positive rank or nonempty spectrum is required. -/
theorem topologicalKrullDim_eq_one_of_mem_irreducibleComponents_finite_flat_polynomial
    {K A : Type*} [Field K] [CommRing A] [Algebra (Polynomial K) A]
    [Module.Finite (Polynomial K) A] [Module.Flat (Polynomial K) A]
    {Z : Set (PrimeSpectrum A)} (hZ : Z ∈ irreducibleComponents (PrimeSpectrum A)) :
    topologicalKrullDim Z = 1 :=
  topologicalKrullDim_eq_one_of_mem_irreducibleComponents_polynomial (K := K) hZ

end PrimeSpectrum
