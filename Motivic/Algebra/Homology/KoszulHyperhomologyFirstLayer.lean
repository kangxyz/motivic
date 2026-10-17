/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulHyperhomologyDegreeZero

/-!
# The first actual homology layer in Koszul Euler devissage

The actual cutoff-one quotient is projected to its degree-zero homology,
then identified with the original complex's degree-zero homology. Tensoring
this genuine quasi-isomorphism proves the first layer's coefficient-Koszul
Euler contribution. Together with the actual canonical truncation short
exact sequence, this removes the original degree-zero homology layer without
assuming its finite length.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex Motivic.LengthEuler

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat R) ℕ) (s : List R)

/-- The actual quotient tensor maps to the coefficient complex on the original `H₀(K)`. -/
noncomputable def firstQuotientTensorToCoefficient :
    HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K 1) ⟶
      coefficientComplex (K.homology 0) s :=
  degreeZeroTensorToCoefficient (truncationQuotient K 1) s ≫
    ((coefficientFunctor s).mapIso (truncationQuotientHomologyIso K 1 0 (by omega)).symm).hom

/-- This comparison is a genuine quasi-isomorphism, with no finiteness assumptions. -/
instance firstQuotientTensorToCoefficient_quasiIso :
    QuasiIso (firstQuotientTensorToCoefficient K s) := by
  have : QuasiIso (degreeZeroTensorToCoefficient (truncationQuotient K 1) s) :=
    degreeZeroTensorToCoefficient_quasiIso _ s (truncationQuotient_exactAt K 1)
  let e : coefficientComplex ((truncationQuotient K 1).homology 0) s ≅
      coefficientComplex (K.homology 0) s :=
    (coefficientFunctor s).mapIso (truncationQuotientHomologyIso K 1 0 (by omega)).symm
  have : QuasiIso e.hom := inferInstance
  exact quasiIso_comp (degreeZeroTensorToCoefficient (truncationQuotient K 1) s) e.hom

/-- The subsequent coefficient-Koszul homology controls finiteness of the first quotient tensor. -/
theorem firstQuotientTensor_finiteHomology
    (hH : FiniteHomology (coefficientComplex (K.homology 0) s)) :
    FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K 1)) :=
  hH.of_iso (fun n => (isoOfQuasiIsoAt (firstQuotientTensorToCoefficient K s) n).symm)

/-- The first quotient tensor has exactly the coefficient-Koszul Euler length of `H₀(K)`. -/
theorem firstQuotientTensor_chainEuler
    (hH : FiniteHomology (coefficientComplex (K.homology 0) s)) :
    chainEuler (HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K 1))
        (firstQuotientTensor_finiteHomology K s hH) =
      chainEuler (coefficientComplex (K.homology 0) s) hH :=
  homologyEuler_eq_of_quasiIso (firstQuotientTensorToCoefficient K s) _ _ hH

/-- The first actual truncation step derives total finiteness and the genuine
coefficient-homology Euler contribution, without finite length of `H₀(K)`. -/
theorem firstTruncation_chainEuler
    (hT : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (K.truncLE (chainPlacement 1))))
    (hH : FiniteHomology (coefficientComplex (K.homology 0) s)) :
    ∃ h : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) K),
      chainEuler (HomologicalComplex.tensorObj (chainComplex s) K) h =
        chainEuler (HomologicalComplex.tensorObj (chainComplex s)
          (K.truncLE (chainPlacement 1))) hT +
        chainEuler (coefficientComplex (K.homology 0) s) hH := by
  refine ⟨truncation_koszulTensor_finiteHomology K 1 s hT
    (firstQuotientTensor_finiteHomology K s hH), ?_⟩
  rw [truncation_koszulTensor_chainEuler K 1 s hT
    (firstQuotientTensor_finiteHomology K s hH), firstQuotientTensor_chainEuler]

end Motivic.Koszul
