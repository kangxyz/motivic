/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Unramified.Field

/-!
# Reducedness of standard-smooth algebras over domains

A flat, essentially finite-type, formally unramified algebra over a domain
embeds into its fraction-field base change. That base change is unramified over
a field and hence reduced. Étale polynomial coordinates therefore prove that
standard-smooth algebras over domains are reduced, without a perfectness
hypothesis on the coefficient field.
-/

@[expose] public section

open scoped TensorProduct

universe u v

section
open _root_.Algebra.FormallyUnramified

/-- A flat unramified algebra over a domain is reduced. The finite-type
hypothesis is essential to the unramified-over-a-field theorem used here. -/
theorem _root_.Algebra.FormallyUnramified.isReduced_of_flat_formallyUnramified
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] : IsReduced S := by
  let K := FractionRing R
  let f : S →ₐ[R] K ⊗[R] S := Algebra.TensorProduct.includeRight
  have : IsReduced (K ⊗[R] S) :=
    Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective f
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- Étale polynomial coordinates make a standard-smooth algebra over any
domain reduced. No irreducibility conclusion is asserted for the algebra. -/
theorem _root_.RingHom.isReduced_of_isStandardSmooth
    {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S) (hf : f.IsStandardSmooth) : IsReduced S := by
  obtain ⟨n, g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) S := hg
  exact isReduced_of_flat_formallyUnramified (MvPolynomial (Fin n) R) S

end
