/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.QuasiFinite.Algebraic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Actual transcendence degree from an étale polynomial chart

A nonempty étale polynomial chart on a domain gives the native transcendence
bound on the original ring, without a separately supplied dimension hypothesis.
-/
@[expose] public noncomputable section

universe u

namespace Algebra

/-- A domain étale over a polynomial algebra in `n` variables has native
transcendence degree exactly `n`. -/
theorem trdeg_eq_of_etale_mvPolynomial
    (k S : Type u) [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    [Etale (MvPolynomial (Fin n) k) S] :
    Algebra.trdeg k S = n := by
  have : Algebra.IsAlgebraic (MvPolynomial (Fin n) k) S :=
    QuasiFinite.isAlgebraic_of_isDomain _ _
  have h := (IsTranscendenceBasis.mvPolynomial (Fin n) k).algebraMap_comp (A := S)
  simpa using h.lift_cardinalMk_eq_trdeg.symm

/-- The preceding result for a specified actual polynomial algebra map. -/
theorem trdeg_eq_of_etale_polynomial_map
    {k S : Type u} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] S) (hf : f.toRingHom.Etale) :
    Algebra.trdeg k S = n := by
  let : Algebra (MvPolynomial (Fin n) k) S := f.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) S :=
    .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Etale (MvPolynomial (Fin n) k) S := hf
  exact trdeg_eq_of_etale_mvPolynomial k S n

/-- An actual étale chart after inverting one nonzero element bounds the
transcendence degree of the original domain, not merely of its localization. -/
theorem trdeg_le_of_etale_localized_polynomial_map
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] R) {r : R} (hr : r ≠ 0)
    (hf : ((algebraMap R (Localization.Away r)).comp f.toRingHom).Etale) :
    Algebra.trdeg k R ≤ n := by
  let S := Localization.Away r
  have : IsDomain S := Localization.Away.isDomain hr
  let j : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  have hdeg : Algebra.trdeg k S = n :=
    trdeg_eq_of_etale_polynomial_map (j.comp f) hf
  exact (trdeg_le_of_injective j
    (IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hr))).trans_eq hdeg

end Algebra
