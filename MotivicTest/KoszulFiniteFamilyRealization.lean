/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteFamilyRealization
public import Motivic.Algebra.Homology.LengthEulerSingle
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Consumers of the bounded-family cycle realization engine

The consumers retain the literal scalar action, one support ideal and one
degree bound. They test signed generic multiplicities, final finiteness with
no intermediate finite-length premise, all maximal branches, an annihilating
zero equation, and the nonlocal two-branch algebra with negative Euler value.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulFiniteFamilyRealization

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- Scalar attachment is the original algebra map, not a supplied equivalent action. -/
theorem originalScalarAction (M : ModuleCat B) (r : R)
    (x : finiteFamilyRestriction R B M) :
    r • x = algebraMap R B r • (x : M) := rfl

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R B]
  (M : ℕ → ModuleCat B) [∀ n, Module.Finite B (M n)]
  (s : List R) (J : Ideal R)
  [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J))]
  (hJ : ∀ n, J ≤ Module.annihilator R (finiteFamilyRestriction R B (M n)))

include hJ in
omit [IsLocalRing R] in
/-- Final whole-algebra finiteness is constructed even though no finite-length
hypothesis is made on any original coefficient module. -/
theorem finalWholeFinite (n : ℕ) :
    FiniteHomology (coefficientComplex (M n) (s.map (algebraMap R B))) :=
  finiteFamilyWhole_finiteHomology R B (M n) s J (hJ n)

include hJ in
omit [IsLocalRing R] in
/-- Every maximal localization is included and receives proved final finiteness. -/
theorem everyFinalBranchFinite (n : ℕ) (q : MaximalSpectrum B) :
    FiniteHomology (finiteFamilyLocalComplex R B (M n) s q) :=
  finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q

omit [IsLocalRing R] in
/-- The first two family degrees contribute a difference of actual generic
lengths, rather than their sum or their unsigned support. -/
theorem twoDegreeGenericSign (p : J.minimalPrimes) :
    finiteFamilyGenericEuler R B M J hJ {0, 1} (fun n => (-1) ^ n) p =
      fixedSupportGenericLength (finiteFamilyRestriction R B (M 0)) J (hJ 0) p -
        fixedSupportGenericLength (finiteFamilyRestriction R B (M 1)) J (hJ 1) p := by
  simp [finiteFamilyGenericEuler, sub_eq_add_neg]

/-- A bounded family gives the complete source and all-maximal-branch equality;
no semilocal enumeration or branch finiteness is an input. -/
theorem boundedActualProjection (N : ℕ) (hzero : ∀ n, N < n → IsZero (M n)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      chainEuler (coefficientComplex (finiteFamilyRestriction R B (M n)) s)
        (finiteFamilyRestriction_finiteHomology R B (M n) s J (hJ n))) =
      ∑ᶠ q : MaximalSpectrum B, (Module.finiteAlgebraResidueDegree R B q : ℤ) *
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * chainEuler (finiteFamilyLocalComplex R B (M n) s q)
          (finiteFamilyLocal_finiteHomology R B (M n) s J (hJ n) q) :=
  boundedFamily_chainEuler_projection R B M s J hJ N hzero

omit [IsLocalRing R] in
/-- Changing the valid common upper bound does not change a generic coefficient. -/
theorem genericCoefficientIndependentOfBound (N N' : ℕ)
    (hzero : ∀ n, N < n → IsZero (M n))
    (hzero' : ∀ n, N' < n → IsZero (M n)) (p : J.minimalPrimes) :
    finiteFamilyGenericEuler R B M J hJ (Finset.range (N + 1)) (fun n => (-1) ^ n) p =
      finiteFamilyGenericEuler R B M J hJ (Finset.range (N' + 1)) (fun n => (-1) ^ n) p := by
  rw [boundedFamilyGenericEuler_eq_finsum R B M J hJ N hzero,
    boundedFamilyGenericEuler_eq_finsum R B M J hJ N' hzero']

section ZeroEquation

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  (C : Type u) [CommRing C] [Algebra A C] [Module.Finite A C]
  (P : ModuleCat C) [Module.Finite C P] (I : Ideal A)
  [IsArtinianRing (A ⧸ (Ideal.ofList ([0] : List A) ⊔ I))]
  (hI : I ≤ Module.annihilator A (finiteFamilyRestriction A C P))

/-- A zero equation is not regular on nonzero coefficients. Its genuine
two-term cancellation is preserved by the all-maximal-branch formula. -/
theorem zeroEquationAllBranches :
    (∑ᶠ q : MaximalSpectrum C, (Module.finiteAlgebraResidueDegree A C q : ℤ) *
      chainEuler (finiteFamilyLocalComplex A C P [0] q)
        (finiteFamilyLocal_finiteHomology A C P [0] I hI q)) = 0 := by
  rw [← finiteFamily_coefficient_projection A C P [0] I hI]
  have : IsArtinianRing (A ⧸ (Ideal.ofList [0] ⊔
      Module.annihilator A (finiteFamilyRestriction A C P))) :=
    koszulDimension_artinian_quotient_of_le _ _ (sup_le_sup_left hI _)
  exact koszulDimension_chainEuler_zero_of_mem_annihilator
    (finiteFamilyRestriction A C P) 0 [] (Ideal.zero_mem _)

end ZeroEquation

section TwoBranches

variable (k : Type u) [Field k]

/-- The empty coefficient complex has exactly its coefficient's finite length. -/
theorem emptyCoefficientEuler (P : ModuleCat k) (hP : Module.length k P ≠ ⊤)
    (h : FiniteHomology (coefficientComplex P [])) :
    chainEuler (coefficientComplex P []) h = integerLength P hP := by
  simpa only [coefficientComplex_nil, pow_zero, one_mul] using
    homologyEuler_single (ComplexShape.down ℕ) 0 P (fun n : ℕ => (-1 : ℤ) ^ n) hP

/-- A genuine nonlocal finite algebra has a signed all-branch value of -2.
The family sign and both branches are retained by the new common engine. -/
theorem twoBranchOddFamily :
    (∑ᶠ q : MaximalSpectrum (k × k),
      (Module.finiteAlgebraResidueDegree k (k × k) q : ℤ) *
        ∑ n ∈ ({1} : Finset ℕ), (-1 : ℤ) ^ n *
          chainEuler (finiteFamilyLocalComplex k (k × k)
            (ModuleCat.of (k × k) (k × k)) [] q)
            (finiteFamilyLocal_finiteHomology k (k × k)
              (ModuleCat.of (k × k) (k × k)) [] ⊥ bot_le q)) = -2 := by
  rw [← finiteFamily_chainEuler_projection k (k × k)
    (fun _ => ModuleCat.of (k × k) (k × k)) [] ⊥ (fun _ => bot_le) {1}
    (fun n => (-1) ^ n)]
  let P := finiteFamilyRestriction k (k × k) (ModuleCat.of (k × k) (k × k))
  have hP : Module.length k P ≠ ⊤ := Module.length_ne_top
  rw [Finset.sum_singleton, emptyCoefficientEuler k P hP]
  let e : P ≃ₗ[k] k × k :=
    { AddEquiv.refl (k × k) with
      map_smul' r m := by
        change (algebraMap k (k × k) r) * (show k × k from m) =
          r • (show k × k from m)
        exact (Algebra.smul_def r (show k × k from m)).symm }
  simp [integerLength, e.length_eq, Module.length_eq_finrank, Module.finrank_prod]

end TwoBranches

end MotivicTest.KoszulFiniteFamilyRealization
