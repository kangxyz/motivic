/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.Normal.LaurentPresentation
public import Lean.Util.CollectAxioms

/-! # Direct tests of the normal-base Laurent quotient presentation -/

@[expose] public noncomputable section

open Polynomial Algebra.NormalLaurentPresentation

universe u v

namespace MotivicTest.NormalLaurentPolynomialPresentation

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  {S : Type v} [CommRing S] [IsDomain S] [Algebra R S]
  [Module.IsTorsionFree R S] [Module.Finite R S]

def actual_finite_quotient (u : Sˣ)
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    AdjoinRoot (minpoly R (u : S)) ≃ₐ[R] S := finiteQuotientEquiv u hs

theorem actual_coordinate (u : Sˣ)
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    actual_finite_quotient u hs (AdjoinRoot.root (minpoly R (u : S))) = (u : S) :=
  finiteQuotientEquiv_root u hs

theorem actual_free_algebra (u : Sˣ)
    (hs : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R S) u)) :
    Module.Free R S := finite_quotient_free u hs

open Lean in
run_cmd do
  for name in #[``reverse_aeval_eq_zero, ``exists_inverse_polynomial,
      ``inverse_mem_adjoin, ``Algebra.NormalLaurentPresentation.adjoin_eq_top,
      ``aeval_surjective, ``minpoly_constant_isUnit, ``evaluation_kernel,
      ``quotientEquiv, ``quotientEquiv_root, ``finiteQuotientEquiv,
      ``finiteQuotientEquiv_root, ``finite_quotient_free, ``exists_monic_presentation,
      ``actual_finite_quotient, ``actual_coordinate, ``actual_free_algebra] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Normal-base Laurent polynomial presentations use only standard Lean foundations."

end MotivicTest.NormalLaurentPolynomialPresentation
