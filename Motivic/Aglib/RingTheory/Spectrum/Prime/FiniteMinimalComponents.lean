/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # Finiteness of the original nonreduced quotient from its minimal components -/
@[expose] public noncomputable section
universe u v
namespace Module

/-- Finite minimal components imply finiteness of the original quotient, with
all its nilpotents retained. No change of the original coefficient algebra is made. -/
theorem finite_quotient_of_minimal_components
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] (I : Ideal B)
    (h : ∀ P ∈ I.minimalPrimes, Module.Finite A (B ⧸ P)) :
    Module.Finite A (B ⧸ I) := by
  classical
  let ι := I.minimalPrimes
  let : Fintype ι := (I.finite_minimalPrimes_of_isNoetherianRing B).fintype
  let (P : ι) : Module.Finite A (B ⧸ P.val) := h P.val P.property
  let f : (B ⧸ I) →ₐ[A] (Π P : ι, B ⧸ P.val) :=
    AlgHom.pi fun P => Ideal.Quotient.factorₐ A P.property.1.2
  have : Module.Finite A f.range :=
    Module.Finite.of_injective f.range.val.toLinearMap Subtype.val_injective
  apply Module.finite_of_surjective_of_ker_le_nilradical f.rangeRestrict
    f.rangeRestrict_surjective ?_ (IsNoetherian.noetherian _)
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hb : b ∈ I.radical := by
    rw [← I.sInf_minimalPrimes, Submodule.mem_sInf]
    intro P hP
    have he := congrArg (fun y : f.range => (y : Π Q : ι, B ⧸ Q.val) ⟨P, hP⟩) hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  obtain ⟨n, hn⟩ := hb
  rw [mem_nilradical]
  exact ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩

end Module
