/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Spectrum.Prime.FiniteMinimalComponents

/-!
# Minimal-prime quotients of finite type algebras
-/

@[expose] public noncomputable section

universe u
namespace RingHom

/-- Finiteness descends from the actual minimal components without changing the
original coefficient homomorphism or deleting nilpotents of the closed quotient. -/
theorem finite_quotient_of_minimal_components
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (I : Ideal B)
    (h : ∀ P ∈ I.minimalPrimes, ((Ideal.Quotient.mk P).comp f).Finite) :
    ((Ideal.Quotient.mk I).comp f).Finite := by
  let : Algebra A B := f.toAlgebra
  have hh : ∀ P ∈ I.minimalPrimes, Module.Finite A (B ⧸ P) := by
    intro P hP
    exact RingHom.finite_algebraMap.mp (h P hP)
  exact RingHom.finite_algebraMap.mpr
    (Module.finite_quotient_of_minimal_components A B I hh)

end RingHom
