/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyBounded

/-!
# Consumers of bounded Koszul hyperhomology

These consumers check the actual tail homology and placement sign, the
finite two-layer formula, and the support-derived two-list formula with
finite coefficients but no finite-length assumption on intermediate homology.
-/

@[expose] public section

universe u

open CategoryTheory
open HomologicalComplex
open _root_.ChainComplex.Koszul
open _root_.HomologicalComplex.ModuleLengthEuler

namespace MotivicTest.KoszulHyperhomologyBounded

variable {R : Type u} [CommRing R]

/-- The actual first tail carries exactly the original degree-one homology. -/
noncomputable def tailDegreeZero (K : ChainComplex (ModuleCat R) ℕ) :
    (homologyTail K).homology 0 ≅ K.homology 1 := homologyTailIso K 0

/-- Actual extension changes the tensor Euler sign even for repeated or zero equations. -/
theorem repeatedZeroPlacement (K : ChainComplex (ModuleCat R) ℕ) (a : R)
    (h : FiniteHomology (tensorObj (chainComplex [a, a, 0]) K)) :
    chainEuler (tensorObj (chainComplex [a, a, 0]) (K.extend (chainPlacement 1)))
        (koszulTensor_placement_finiteHomology K [a, a, 0] h) =
      -chainEuler (tensorObj (chainComplex [a, a, 0]) K) h :=
  koszulTensor_placement_chainEuler K [a, a, 0] h

/-- The actual bounded induction produces the difference of two homology layers. -/
theorem twoLayers (K : ChainComplex (ModuleCat R) ℕ) (s : List R)
    (hK : ∀ n, 1 < n → K.ExactAt n)
    (hH : ∀ n, n ≤ 1 → FiniteHomology (coefficientComplex (K.homology n) s)) :
    ∃ h : FiniteHomology (tensorObj (chainComplex s) K),
      chainEuler (tensorObj (chainComplex s) K) h =
        chainEuler (coefficientComplex (K.homology 0) s) (hH 0 (by omega)) -
        chainEuler (coefficientComplex (K.homology 1) s) (hH 1 (by omega)) := by
  obtain ⟨h, he⟩ := bounded_koszulTensor_chainEuler K s 1 hK hH
  refine ⟨h, ?_⟩
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using he

/-- Empty subsequent equations remain covered by the true bounded statement. -/
theorem emptySecondList (K : ChainComplex (ModuleCat R) ℕ) (N : ℕ)
    (hK : ∀ n, N < n → K.ExactAt n)
    (hH : ∀ n, n ≤ N → FiniteHomology (coefficientComplex (K.homology n) [])) :
    FiniteHomology (tensorObj (chainComplex ([] : List R)) K) :=
  bounded_koszulTensor_finiteHomology K [] N hK hH

/-- Two actual zero equations at the first stage are allowed. Intermediate
homology finiteness is derived only after applying the second equation list. -/
theorem zeroFirstEquations [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList [0, 0] ⊔ Module.annihilator R M)))] :
    ∃ h : FiniteHomology (tensorObj (chainComplex s) (coefficientComplex M [0, 0])),
      chainEuler (tensorObj (chainComplex s) (coefficientComplex M [0, 0])) h =
        ∑ n : Fin 3, (-1 : ℤ) ^ (n : ℕ) *
          chainEuler (coefficientComplex ((coefficientComplex M [0, 0]).homology n) s)
            (coefficient_homology_koszul_finiteHomology M s [0, 0] n) :=
  coefficient_koszulTensor_chainEuler M s [0, 0]

end MotivicTest.KoszulHyperhomologyBounded
