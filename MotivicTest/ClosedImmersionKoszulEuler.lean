/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Multiplicity.ClosedImmersionKoszulEuler
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Mathlib.Data.ZMod.Basic

/-!
# Closed-support Euler consumers

The consumers keep the actual closed immersion and stalk list. They cover a
nonreduced ambient scheme, the empty closed support, supports missing all
ambient component generics, and a finite family with negative integer weights.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry _root_.HomologicalComplex.ModuleLengthEuler

universe u

namespace Motivic.MotivicTest.ClosedImmersionKoszulEuler
open _root_.AlgebraicGeometry.Scheme (IntegralCycle)

/-- The nonreduced affine scheme `Spec (ZMod 4)`. -/
abbrev doublePoint : Scheme := Spec (.of (ZMod 4))

/-- `Spec (ZMod 4)` comes from a ring with a nonzero square-zero element. -/
theorem nonreduced_witness : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide

/-- The extraction specializes to the unreduced ambient scheme itself, without
changing its stalk to the stalk of its reduction. -/
theorem nonreduced_identity
    (x : doublePoint) (s : List (doublePoint.presheaf.stalk x))
    [IsArtinianRing ((doublePoint.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))]
    (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal
      (doublePoint.presheaf.stalk x)) :
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of (doublePoint.presheaf.stalk x)
          ((doublePoint.presheaf.stalk x) ⧸
            (𝟙 doublePoint : doublePoint ⟶ doublePoint).ker.stalk x)) s)
        (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥
            bot_le) =
      ∑ᶠ q : {q : genericPoints doublePoint // q.1 ⤳ x},
        IntegralCycle.toPoints (_root_.AlgebraicGeometry.Scheme.fundamentalCycle doublePoint) q.1.1
            *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of (doublePoint.presheaf.stalk x)
              ((doublePoint.presheaf.stalk x) ⧸
                (_root_.AlgebraicGeometry.Scheme.genericStalkLocalizationPrime doublePoint x
                    q).asIdeal)) s)
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology s ⊥
              (_root_.AlgebraicGeometry.Scheme.genericStalkLocalizationPrime doublePoint x
                  q).asIdeal bot_le) := by
  simpa only [IntegralCycle.finitePushforward_id, AddMonoidHom.id_apply] using
    closedImmersion_chainEuler_replacement (𝟙 doublePoint : doublePoint ⟶ doublePoint) x s hs

/-- A lower-dimensional closed support containing no ambient component through
`x` has zero Euler test. Generic preservation of the closed immersion is not needed. -/
theorem no_ambient_component {E P : Scheme.{u}}
    [IsNoetherian E] [IsLocallyNoetherian P] (j : E ⟶ P) [IsClosedImmersion j]
    (x : P) (s : List (P.presheaf.stalk x))
    [IsArtinianRing ((P.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))]
    (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk x))
    (himage : ∀ q : {q : genericPoints P // q.1 ⤳ x}, q.1.1 ∉ Set.range j) :
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) ((P.presheaf.stalk x) ⧸ j.ker.stalk x)) s)
        (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥
            bot_le) = 0 := by
  rw [closedImmersion_chainEuler_replacement j x s hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  rw [
  _root_.AlgebraicGeometry.Scheme.Hom.closedImmersion_fundamentalCoefficient_eq_stalkQuotientLength,
    _root_.AlgebraicGeometry.Scheme.Hom.closedImmersion_ker_stalk_eq_top j (himage q)]
  simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, zero_mul]

/-- The actual unit-ideal closed subscheme is an empty support with zero Euler
characteristic, including in a nonreduced ambient scheme. -/
theorem empty_closed_support {P : Scheme.{u}} [IsNoetherian P]
    (x : P) (s : List (P.presheaf.stalk x))
    [IsArtinianRing ((P.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))]
    (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk x)) :
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) ((P.presheaf.stalk x) ⧸
          (⊤ : P.IdealSheafData).subschemeι.ker.stalk x)) s)
        (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥
            bot_le) = 0 := by
  let : IsNoetherian (⊤ : P.IdealSheafData).subscheme :=
    _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (⊤ : P.IdealSheafData).subschemeι
  exact no_ambient_component (⊤ : P.IdealSheafData).subschemeι x s hs
    (fun _ ⟨y, _⟩ ↦ isEmptyElim y)

/-- Finite signed coefficients are used as integers, and the identity case
really acts on the regular stalk module. -/
theorem signed_identity_family {P : Scheme.{u}} [IsNoetherian P]
    (x : P) (s : List (P.presheaf.stalk x))
    [IsArtinianRing ((P.presheaf.stalk x) ⧸ (Ideal.ofList s ⊔ ⊥))]
    (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk x)) :
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) (P.presheaf.stalk x)) s)
        (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s ⊥
            bot_le) =
      ∑ i : Fin 2, (![2, -1] : Fin 2 → ℤ) i *
        chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
          (ModuleCat.of (P.presheaf.stalk x)
            ((P.presheaf.stalk x) ⧸ (𝟙 P : P ⟶ P).ker.stalk x)) s)
          (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ s
              ⊥ bot_le) := by
  apply chainEuler_eq_sum_of_fundamentalCycle_eq (fun _ : Fin 2 ↦ P)
    (fun _ ↦ 𝟙 P) (![2, -1]) _ x s hs
  simp [Fin.sum_univ_two, two_smul]

open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.stalkMinimalPrimeGenericEquiv,
      ``AlgebraicGeometry.stalkMinimalPrimeGenericEquiv_symm_val,
      ``AlgebraicGeometry.finite_genericPoints_specializing,
      ``AlgebraicGeometry.closedImmersion_chainEuler_replacement,
      ``AlgebraicGeometry.closedImmersion_chainEuler_eq_sum_of_fundamentalCycle_eq,
      ``AlgebraicGeometry.id_closedImmersion_chainEuler_eq,
      ``AlgebraicGeometry.chainEuler_eq_sum_of_fundamentalCycle_eq,
      ``nonreduced_witness, ``nonreduced_identity, ``no_ambient_component,
      ``empty_closed_support, ``signed_identity_family] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Closed-support Euler extraction and consumers use only standard foundations."

end Motivic.MotivicTest.ClosedImmersionKoszulEuler
