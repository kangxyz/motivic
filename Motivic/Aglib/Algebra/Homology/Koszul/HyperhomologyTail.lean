/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyFirstLayer

/-!
# Actual homology of the reindexed canonical tail

The restricted canonical truncation retaining degrees at least one is an
actual nonnegative complex whose degree-`n` homology is the original
`H_{n+1}`. This comparison uses the extension homology isomorphism, the actual
truncation/extension isomorphism, and the quasi-isomorphism induced by the
canonical truncation inclusion in every retained degree.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat R) ℕ)

/-- The actual canonical tail, reindexed to begin in degree zero. -/
noncomputable abbrev homologyTail : ChainComplex (ModuleCat R) ℕ :=
  K.truncLE' (chainPlacement 1)

/-- The tail has the actual next-degree homology of the original complex. -/
noncomputable def homologyTailIso (n : ℕ) :
    (homologyTail K).homology n ≅ K.homology (n + 1) := by
  have : QuasiIsoAt (K.ιTruncLE (chainPlacement 1)) (n + 1) :=
    K.quasiIsoAt_ιTruncLE (chainPlacement 1) (j := n) rfl
  exact ((homologyTail K).extendHomologyIso (chainPlacement 1) (j' := n + 1) rfl).symm ≪≫
    (homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) (n + 1)).mapIso
      (K.truncLEIso (chainPlacement 1)).symm ≪≫
    isoOfQuasiIsoAt (K.ιTruncLE (chainPlacement 1)) (n + 1)

/-- Exactness of the actual tail is precisely next-degree exactness. -/
theorem homologyTail_exactAt_iff (n : ℕ) :
    (homologyTail K).ExactAt n ↔ K.ExactAt (n + 1) := by
  rw [exactAt_iff_isZero_homology, exactAt_iff_isZero_homology]
  exact (homologyTailIso K n).isZero_iff

/-- The homological upper bound decreases by one in the actual reindexed tail. -/
theorem homologyTail_exactAt_above (N : ℕ)
    (hK : ∀ n, N + 1 < n → K.ExactAt n) (n : ℕ) (hn : N < n) :
    (homologyTail K).ExactAt n :=
  (homologyTail_exactAt_iff K n).mpr (hK (n + 1) (by omega))

/-- The coefficient-Koszul complex on a tail homology module is actually isomorphic
to the next original coefficient-Koszul complex. -/
noncomputable def homologyTailCoefficientIso (s : List R) (n : ℕ) :
    coefficientComplex ((homologyTail K).homology n) s ≅
      coefficientComplex (K.homology (n + 1)) s :=
  (coefficientFunctor s).mapIso (homologyTailIso K n)

/-- Finite coefficient-Koszul homology transfers to the actual reindexed tail. -/
theorem homologyTailCoefficient_finiteHomology (s : List R) (n : ℕ)
    (hH : FiniteHomology (coefficientComplex (K.homology (n + 1)) s)) :
    FiniteHomology (coefficientComplex ((homologyTail K).homology n) s) :=
  hH.of_iso (fun j => ((homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) j).mapIso
    (homologyTailCoefficientIso K s n)).symm)

/-- The coefficient Euler contribution of the tail equals the next original contribution. -/
theorem homologyTailCoefficient_chainEuler (s : List R) (n : ℕ)
    (hH : FiniteHomology (coefficientComplex (K.homology (n + 1)) s)) :
    chainEuler (coefficientComplex ((homologyTail K).homology n) s)
        (homologyTailCoefficient_finiteHomology K s n hH) =
      chainEuler (coefficientComplex (K.homology (n + 1)) s) hH :=
  homologyEuler_eq_of_quasiIso (homologyTailCoefficientIso K s n).hom _ _ hH

/-- The actual tensor of the canonical truncation is isomorphic to the tensor
of the placed tail, before any Euler characteristic is taken. -/
noncomputable def homologyTailTensorTruncationIso (s : List R) :
    tensorObj (chainComplex s) (K.truncLE (chainPlacement 1)) ≅
      tensorObj (chainComplex s) ((homologyTail K).extend (chainPlacement 1)) :=
  (koszulTensorFunctor s).mapIso (K.truncLEIso (chainPlacement 1))

end ChainComplex.Koszul
