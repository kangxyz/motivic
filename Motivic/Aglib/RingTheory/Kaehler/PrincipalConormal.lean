/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Regular.Basic

/-! # The original regular equation in its conormal module -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential

universe u v

namespace Ideal

/-- Division by a regular generator is a linear isomorphism with its actual ideal. -/
def regularGeneratorEquiv {R : Type u} [CommRing R] (t : R) (ht : IsRegular t) :
    R ≃ₗ[R] Ideal.span {t} := by
  let m : R →ₗ[R] Ideal.span {t} :=
    (LinearMap.toSpanSingleton R R t).codRestrict _ (fun r ↦ by
      change r * t ∈ Ideal.span {t}
      exact Ideal.mul_mem_left _ r (Ideal.subset_span (by simp)))
  apply LinearEquiv.ofBijective m
  constructor
  · intro x y h
    exact ht.right (congrArg Subtype.val h)
  · intro x
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp x.property
    exact ⟨r, Subtype.ext (by simpa [m, mul_comm] using hr.symm)⟩

@[simp]
theorem regularGeneratorEquiv_apply {R : Type u} [CommRing R] (t : R) (ht : IsRegular t)
    (r : R) : (regularGeneratorEquiv t ht r : R) = r * t := rfl

/-- The class of the original equation has coefficient one in the conormal
module of its original principal ideal. -/
theorem exists_conormal_functional_regular_generator {R : Type u} [CommRing R]
    (t : R) (ht : IsRegular t) :
    ∃ l : (Ideal.span {t}).Cotangent →ₗ[R] R ⧸ Ideal.span {t},
      l ((Ideal.span {t}).toCotangent ⟨t, Ideal.subset_span (by simp)⟩) = 1 := by
  let I : Ideal R := Ideal.span {t}
  let e := regularGeneratorEquiv t ht
  let d : I →ₗ[R] R ⧸ I :=
    (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ e.symm.toLinearMap
  have hd (x y : I) : d (x * y) = 0 := by
    have hm : x * y = (x : R) • y := by ext; rfl
    rw [hm, map_smul]
    change Ideal.Quotient.mk I (x : R) * d y = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]
  refine ⟨Ideal.Cotangent.lift d hd, ?_⟩
  rw [Ideal.Cotangent.lift_toCotangent]
  have he : (⟨t, Ideal.subset_span (by simp)⟩ : I) = e 1 := by ext; simp [e]
  rw [he]
  simp [d]

end Ideal

namespace Algebra.FormallySmooth

/-- A smooth principal quotient makes its unchanged regular equation a unimodular
differential along the entire quotient, not only at rational points. -/
theorem exists_quotient_differential_functional
    (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Algebra k R]
    [FormallySmooth k R] (t : R) (ht : IsRegular t)
    [FormallySmooth k (R ⧸ Ideal.span {t})] :
    ∃ l : (R ⧸ Ideal.span {t}) ⊗[R] Ω[R⁄k] →ₗ[R] R ⧸ Ideal.span {t},
      l (1 ⊗ₜ D k R t) = 1 := by
  let I : Ideal R := Ideal.span {t}
  let Q := R ⧸ I
  have hk : RingHom.ker (algebraMap R Q) = I := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  obtain ⟨s, hs⟩ := (iff_split_injection (R := k) (P := R) (A := Q)
    (Ideal.Quotient.mk_surjective)).mp inferInstance
  obtain ⟨d, hd⟩ := Ideal.exists_conormal_functional_regular_generator t ht
  let e := Ideal.Cotangent.equivOfEq _ I hk
  let x : RingHom.ker (algebraMap R Q) := ⟨t, by rw [hk]; exact Ideal.subset_span (by simp)⟩
  refine ⟨d ∘ₗ e.toLinearMap ∘ₗ s, ?_⟩
  have hx := LinearMap.congr_fun hs ((RingHom.ker (algebraMap R Q)).toCotangent x)
  change s (1 ⊗ₜ D k R t) = _ at hx
  simp only [LinearMap.comp_apply]
  rw [hx]
  change d (e ((RingHom.ker (algebraMap R Q)).toCotangent x)) = 1
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  convert hd using 2
  congr 1

end Algebra.FormallySmooth

namespace Algebra.FormallySmooth

/-- The specified differential stays nonzero over every field-valued point of
the actual divisor. No separability or rationality of that point is needed. -/
theorem tensor_differential_ne_zero_of_regular_quotient
    (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Algebra k R]
    [FormallySmooth k R] (t : R) (ht : IsRegular t)
    [FormallySmooth k (R ⧸ Ideal.span {t})]
    (K : Type*) [Field K] [Algebra R K] (htK : algebraMap R K t = 0) :
    (1 ⊗ₜ[R] D k R t : K ⊗[R] Ω[R⁄k]) ≠ 0 := by
  let I : Ideal R := Ideal.span {t}
  have hI : ∀ x : R, x ∈ I → algebraMap R K x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    simp [htK]
  let q : R ⧸ I →ₐ[R] K := Ideal.Quotient.liftₐ I (Algebra.ofId R K) hI
  obtain ⟨l, hl⟩ := exists_quotient_differential_functional k R t ht
  let d : Ω[R⁄k] →ₗ[R] K := q.toLinearMap ∘ₗ l ∘ₗ TensorProduct.mk R (R ⧸ I) Ω[R⁄k] 1
  have hd : d (D k R t) = 1 := by
    change q (l (1 ⊗ₜ D k R t)) = 1
    rw [hl, map_one]
  intro h
  have hh := congrArg (d.liftBaseChange K) h
  simp only [LinearMap.liftBaseChange_tmul, one_smul, map_zero, hd] at hh
  exact one_ne_zero hh

end Algebra.FormallySmooth
