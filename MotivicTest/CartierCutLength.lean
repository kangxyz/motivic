/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.CartierCutLength
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Consumers of genuine singleton Cartier-cut length

The original ring and support ideal remain unchanged. The tests separately
retain finite-length evidence and integer Euler equality, and allow a
nonreduced ring as well as the empty closed support.
-/

@[expose] public noncomputable section

open CategoryTheory Motivic Motivic.LengthEuler

universe u

namespace Motivic.MotivicTest.CartierCutLength

variable {R : Type u} [CommRing R]

/-- The quotient result accepts any proof of finite actual Koszul homology. -/
theorem original_support (J : Ideal R) (t : R)
    (ht : IsSMulRegular (R ⧸ J) t)
    (h : FiniteHomology (Koszul.coefficientComplex (ModuleCat.of R (R ⧸ J)) [t])) :
    Module.length R (R ⧸ (Ideal.ofList [t] ⊔ J)) ≠ ⊤ ∧
      chainEuler (Koszul.coefficientComplex (ModuleCat.of R (R ⧸ J)) [t]) h =
        ((Module.length R (R ⧸ (Ideal.ofList [t] ⊔ J))).toNat : ℤ) :=
  ⟨Koszul.singleton_cut_length_ne_top J t ht h,
    Koszul.singleton_chainEuler_eq_quotient_length J t ht h⟩

/-- The test coefficient ring contains a nonzero square-zero element. -/
theorem nonreduced_witness : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide

/-- The polynomial fiber over the nonreduced ring is actually finite and Artinian. -/
theorem nonreduced_polynomial_cut_artinian :
    IsArtinianRing (Polynomial (ZMod 4) ⧸ Ideal.ofList [(Polynomial.X : Polynomial (ZMod 4))]) := by
  have : Finite (Polynomial (ZMod 4) ⧸
      Ideal.span {Polynomial.X - Polynomial.C (0 : ZMod 4)}) :=
    Finite.of_equiv (ZMod 4) (Polynomial.quotientSpanXSubCAlgEquiv 0).symm.toEquiv
  have : Finite (Polynomial (ZMod 4) ⧸ Ideal.ofList [(Polynomial.X : Polynomial (ZMod 4))]) := by
    simpa only [Polynomial.C_0, sub_zero, Ideal.ofList_singleton] using this
  infer_instance

/-- Finiteness for the original nonreduced polynomial singleton is derived,
not assumed through a numeric length conversion. -/
theorem nonreduced_polynomial_finite :
    FiniteHomology (Koszul.coefficientComplex
      (ModuleCat.of (Polynomial (ZMod 4)) (Polynomial (ZMod 4))) [Polynomial.X]) := by
  have : IsArtinianRing (Polynomial (ZMod 4) ⧸
      (Ideal.ofList [(Polynomial.X : Polynomial (ZMod 4))] ⊔
        (⊥ : Ideal (Polynomial (ZMod 4))))) := by
    rw [sup_bot_eq]
    exact nonreduced_polynomial_cut_artinian
  exact Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le

/-- A regular equation over a genuinely nonreduced coefficient ring uses the
unreduced scalar quotient and its full finite length. -/
theorem nonreduced_polynomial :
    chainEuler (Koszul.coefficientComplex
      (ModuleCat.of (Polynomial (ZMod 4)) (Polynomial (ZMod 4))) [Polynomial.X])
        nonreduced_polynomial_finite =
      ((Module.length (Polynomial (ZMod 4))
        (Polynomial (ZMod 4) ⧸ Ideal.ofList [(Polynomial.X : Polynomial (ZMod 4))])).toNat : ℤ) :=
  Koszul.singleton_chainEuler_eq_ring_quotient_length _
    Polynomial.isRegular_X.left.isSMulRegular _

/-- Flat polynomial fibers remain regular on every original component. -/
theorem flat_polynomial_component {k A : Type u} [CommRing k] [CommRing A]
    [Algebra (Polynomial k) A] [Module.Flat (Polynomial k) A]
    (a : k) {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    IsSMulRegular (A ⧸ p)
      (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C a)) :=
  (IsSMulRegular.polynomial_fiber_of_flat a).quotient_of_mem_minimalPrimes hp

/-- Empty closed support has actual finite homology. -/
theorem empty_support_finite [IsNoetherianRing R] (t : R) :
    FiniteHomology (Koszul.coefficientComplex (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) [t]) := by
  have : IsArtinianRing (R ⧸ (Ideal.ofList [t] ⊔ (⊤ : Ideal R))) := by
    rw [sup_top_eq]
    infer_instance
  exact Koszul.singleton_quotient_finiteHomology_of_artinian (⊤ : Ideal R) t

/-- Empty closed support gives zero and does not need a nontriviality hypothesis. -/
theorem empty_support [IsNoetherianRing R] (t : R) :
    chainEuler (Koszul.coefficientComplex (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) [t])
      (empty_support_finite t) = 0 := by
  rw [Koszul.singleton_chainEuler_eq_quotient_length (⊤ : Ideal R) t
    (fun _ _ _ => Subsingleton.elim _ _)]
  simp

open Lean in
run_cmd do
  for name in #[``Koszul.nil_chainEuler_eq_length,
      ``Koszul.singleton_quotient_length_ne_top,
      ``Koszul.singleton_finiteHomology_of_regular,
      ``Koszul.singleton_chainEuler_eq_length,
      ``Koszul.singleQuotientQuotientEquiv,
      ``Koszul.singleQuotientRingEquiv,
      ``Koszul.singleton_chainEuler_eq_ring_quotient_length,
      ``Koszul.singleton_cut_length_ne_top,
      ``Koszul.singleton_chainEuler_eq_quotient_length,
      ``Koszul.singleton_quotient_finiteHomology_of_artinian,
      ``Koszul.singleton_chainEuler_eq_quotient_length_of_artinian,
      ``IsSMulRegular.quotient_of_mem_minimalPrimes,
      ``IsSMulRegular.polynomial_fiber_of_flat,
      ``original_support, ``nonreduced_witness, ``nonreduced_polynomial_cut_artinian,
      ``nonreduced_polynomial_finite, ``nonreduced_polynomial,
      ``flat_polynomial_component, ``empty_support_finite, ``empty_support] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual Cartier-cut lengths and consumers use only standard foundations."

end Motivic.MotivicTest.CartierCutLength
