/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Tactic.LinearCombination

/-!
# Monic presentations of finite integral Laurent quotients over normal domains

An invertible integral coordinate whose inverse is integral generates the same
algebra by ordinary polynomials as by Laurent polynomials. Over an integrally
closed domain its actual minimal polynomial has invertible constant term and
generates the kernel of evaluation. No monic presentation is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

universe u v

namespace Algebra.NormalLaurentPresentation

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- Reversing any relation on the inverse gives a relation on the original unit. -/
theorem reverse_aeval_eq_zero (u : Sˣ) {p : R[X]}
    (hp : aeval (↑(u⁻¹) : S) p = 0) : aeval (u : S) p.reverse = 0 := by
  have h := (eval₂_reverse_eq_zero_iff (algebraMap R S) (↑(u⁻¹) : S) p).mpr hp
  simpa only [invOf_units, inv_inv, aeval_def] using h

/-- Integrality of the inverse produces an actual polynomial expression for it. -/
theorem exists_inverse_polynomial (u : Sˣ) (hi : IsIntegral R (↑(u⁻¹) : S)) :
    ∃ p : R[X], aeval (u : S) p = (↑(u⁻¹) : S) := by
  obtain ⟨q, hq, he⟩ := hi
  have hr := reverse_aeval_eq_zero u he
  have h0 : q.reverse.coeff 0 = 1 := (coeff_zero_reverse q).trans hq
  have h := congrArg (aeval (u : S)) (X_mul_divX_add q.reverse)
  simp only [map_add, map_mul, aeval_X, h0, map_one, hr] at h
  refine ⟨-q.reverse.divX, ?_⟩
  apply u.mul_right_inj.mp
  rw [map_neg, mul_neg, u.mul_inv]
  linear_combination -h

/-- The inverse belongs to the ordinary polynomial subalgebra, without a field hypothesis. -/
theorem inverse_mem_adjoin (u : Sˣ) (hi : IsIntegral R (↑(u⁻¹) : S)) :
    (↑(u⁻¹) : S) ∈ Algebra.adjoin R {(u : S)} := by
  obtain ⟨p, hp⟩ := exists_inverse_polynomial u hi
  rw [← hp]
  exact aeval_mem_adjoin_singleton R _

/-- Laurent generation and integrality of the inverse imply ordinary polynomial generation. -/
theorem adjoin_eq_top (u : Sˣ) (hi : IsIntegral R (↑(u⁻¹) : S))
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    Algebra.adjoin R {(u : S)} = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨p, rfl⟩ := hs x
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using Subalgebra.add_mem _ hp hq
  | C_mul_T n a =>
    rw [LaurentPolynomial.eval₂_C_mul_T]
    apply Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a)
    cases n with
    | ofNat n =>
      simpa using
        Subalgebra.pow_mem _ (Algebra.subset_adjoin rfl :
          (u : S) ∈ Algebra.adjoin R {(u : S)}) n
    | negSucc n =>
      simpa [zpow_negSucc] using
        Subalgebra.pow_mem _ (inverse_mem_adjoin u hi) (n + 1)

/-- Surjectivity is for the literal evaluation at the given Laurent coordinate. -/
theorem aeval_surjective (u : Sˣ) (hi : IsIntegral R (↑(u⁻¹) : S))
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    Function.Surjective (aeval (R := R) (u : S)) := by
  apply (AlgHom.range_eq_top _).mp
  rw [← Algebra.adjoin_singleton_eq_range_aeval, adjoin_eq_top u hi hs]

variable [IsDomain R] [IsIntegrallyClosed R] [IsDomain S] [Module.IsTorsionFree R S]

/-- The constant coefficient of the actual minimal polynomial is a unit. -/
theorem minpoly_constant_isUnit (u : Sˣ) (hu : IsIntegral R (u : S))
    (hi : IsIntegral R (↑(u⁻¹) : S)) : IsUnit ((minpoly R (u : S)).coeff 0) := by
  have hr := reverse_aeval_eq_zero u (minpoly.aeval R (↑(u⁻¹) : S))
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hu hr
  have h := congrArg (fun p : R[X] => p.coeff 0) hq
  rw [coeff_zero_reverse, (minpoly.monic hi).leadingCoeff, mul_coeff_zero] at h
  exact isUnit_of_dvd_one ⟨q.coeff 0, h⟩

/-- The original Laurent coordinate has exactly the monic minimal-polynomial kernel. -/
theorem evaluation_kernel (u : Sˣ) (hu : IsIntegral R (u : S)) :
    RingHom.ker (aeval (R := R) (u : S)).toRingHom =
      Ideal.span ({minpoly R (u : S)} : Set R[X]) := minpoly.ker_eval hu

/-- The entire original algebra, not its reduction, is the minimal-polynomial quotient. -/
def quotientEquiv (u : Sˣ) (hu : IsIntegral R (u : S))
    (hi : IsIntegral R (↑(u⁻¹) : S))
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    AdjoinRoot (minpoly R (u : S)) ≃ₐ[R] S :=
  (minpoly.equivAdjoin hu).trans
    ((Subalgebra.equivOfEq _ _ (adjoin_eq_top u hi hs)).trans Subalgebra.topEquiv)

@[simp] theorem quotientEquiv_root (u : Sˣ) (hu : IsIntegral R (u : S))
    (hi : IsIntegral R (↑(u⁻¹) : S))
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    quotientEquiv u hu hi hs (AdjoinRoot.root (minpoly R (u : S))) = (u : S) := by
  change ((minpoly.equivAdjoin hu) (AdjoinRoot.root (minpoly R (u : S)))).val = (u : S)
  change ((AdjoinRoot.Minpoly.toAdjoin R (u : S))
    (AdjoinRoot.root (minpoly R (u : S)))).val = (u : S)
  simp [AdjoinRoot.Minpoly.toAdjoin]

variable [Module.Finite R S]

/-- Finiteness supplies both integral relations; the original coordinate supplies the quotient. -/
def finiteQuotientEquiv (u : Sˣ)
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    AdjoinRoot (minpoly R (u : S)) ≃ₐ[R] S :=
  quotientEquiv u (Algebra.IsIntegral.isIntegral _) (Algebra.IsIntegral.isIntegral _) hs

@[simp] theorem finiteQuotientEquiv_root (u : Sˣ)
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    finiteQuotientEquiv u hs (AdjoinRoot.root (minpoly R (u : S))) = (u : S) :=
  quotientEquiv_root u _ _ hs

/-- Such finite integral Laurent quotients are actually free over the normal base. -/
theorem finite_quotient_free (u : Sˣ)
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    Module.Free R S :=
  Module.Free.of_basis
    (PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral (u : S))
      (adjoin_eq_top u (Algebra.IsIntegral.isIntegral _) hs)).basis

/-- The monic constant-unit polynomial and coordinate-preserving quotient are constructed. -/
theorem exists_monic_presentation (u : Sˣ)
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    ∃ p : R[X], p.Monic ∧ IsUnit (p.coeff 0) ∧ 0 < p.natDegree ∧
      ∃ e : AdjoinRoot p ≃ₐ[R] S, e (AdjoinRoot.root p) = (u : S) := by
  have hu : IsIntegral R (u : S) := Algebra.IsIntegral.isIntegral _
  exact ⟨minpoly R (u : S), minpoly.monic hu,
    minpoly_constant_isUnit u hu (Algebra.IsIntegral.isIntegral _),
    minpoly.natDegree_pos hu, finiteQuotientEquiv u hs, finiteQuotientEquiv_root u hs⟩

end Algebra.NormalLaurentPresentation
