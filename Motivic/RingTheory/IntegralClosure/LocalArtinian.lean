/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Local relative normality inside a reduced Artinian algebra

A local ring integrally closed in a reduced Artinian algebra is an integrally
closed domain. Idempotents of the ambient algebra are integral, so they descend
to the local ring and must be zero or one. The Artinian product decomposition
then has a unique residue-field factor. Nontriviality of the ambient algebra
is derived from the injectivity included in relative integral closedness.
-/

@[expose] public section

universe u v

namespace Motivic

variable {C : Type u} {D : Type v} [CommRing C] [CommRing D]

/-- An idempotent of an algebra is integral over its scalar ring. -/
theorem isIntegral_of_isIdempotentElem [Algebra C D] {e : D}
    (he : IsIdempotentElem e) : IsIntegral C e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simp [mul_sub, he.eq]

/-- Idempotents of a local ring are zero or one; no domain assumption is needed. -/
theorem eq_zero_or_one_of_isIdempotentElem [IsLocalRing C] {e : C}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (h.mul_left_cancel (by simpa using he.eq))
  · exact Or.inl (h.mul_left_cancel (by simpa using he.one_sub_mul_self))

/-- Relative integral closedness over a local ring forces every ambient
idempotent to be zero or one. -/
theorem eq_zero_or_one_of_local_integrallyClosedIn [Algebra C D]
    [IsLocalRing C] [IsIntegrallyClosedIn C D] {e : D}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  obtain ⟨hinj, hcl⟩ := (isIntegrallyClosedIn_iff (R := C) (A := D)).mp inferInstance
  obtain ⟨c, hc⟩ := hcl (isIntegral_of_isIdempotentElem (C := C) he)
  have hci : IsIdempotentElem c := by
    apply hinj
    simpa only [map_mul, hc] using he.eq
  rcases eq_zero_or_one_of_isIdempotentElem hci with h | h
  · left
    rw [← hc, h, map_zero]
  · right
    rw [← hc, h, map_one]

/-- A reduced Artinian algebra integrally closed over a local scalar ring is a
field. Nontriviality follows from the injection of the local scalar ring. -/
theorem isField_of_local_integrallyClosedIn_artinian (C D : Type*)
    [CommRing C] [CommRing D] [Algebra C D] [IsLocalRing C]
    [IsIntegrallyClosedIn C D] [IsReduced D] [IsArtinianRing D] : IsField D := by
  classical
  have hinj := IsIntegralClosure.algebraMap_injective C C D
  have : Nontrivial D := hinj.nontrivial
  let f := IsArtinianRing.equivPi D
  have : Subsingleton (MaximalSpectrum D) := ⟨fun m n => by
    by_contra hmn
    let p : ∀ j : MaximalSpectrum D, D ⧸ j.asIdeal := fun j => if j = m then 1 else 0
    have hp : IsIdempotentElem p := by
      funext j
      by_cases hj : j = m <;> simp [p, hj]
    have he := eq_zero_or_one_of_local_integrallyClosedIn (C := C) (hp.map f.symm)
    rcases he with he | he
    · have hz := congrArg (fun x => f x m) he
      let := IsArtinianRing.fieldOfSubtypeIsMaximal D m
      simp [p] at hz
    · have ho := congrArg (fun x => f x n) he
      let := IsArtinianRing.fieldOfSubtypeIsMaximal D n
      simp [p, Ne.symm hmn] at ho⟩
  have : IsLocalRing D := IsLocalRing.of_singleton_maximalSpectrum
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing D

/-- A local ring integrally closed in a reduced Artinian algebra is an
integrally closed domain. The ambient algebra need not initially be a field. -/
theorem normalDomain_of_local_integrallyClosedIn_artinian (C D : Type*)
    [CommRing C] [CommRing D] [Algebra C D] [IsLocalRing C]
    [IsIntegrallyClosedIn C D] [IsReduced D] [IsArtinianRing D] :
    IsDomain C ∧ IsIntegrallyClosed C := by
  let := (isField_of_local_integrallyClosedIn_artinian C D).toField
  have hinj := IsIntegralClosure.algebraMap_injective C C D
  have : FaithfulSMul C D := (faithfulSMul_iff_algebraMap_injective C D).mpr hinj
  exact ⟨hinj.isDomain _, IsIntegrallyClosed.of_isIntegrallyClosedIn C D⟩

end Motivic
