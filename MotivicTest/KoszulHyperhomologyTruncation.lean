/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulHyperhomologyTruncation

/-!
# Consumers of genuine Koszul-tensored truncation sequences

These examples use the canonical truncation subcomplex and its actual
cokernel. The original complex has no finite-length homology assumption.
The equations may include both repetition and zero.
-/

@[expose] public section

universe u

open CategoryTheory Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulHyperhomologyTruncation

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat R) ℕ)

/-- The actual degree-one truncation quotient retains precisely degree-zero homology. -/
theorem degreeZeroHomologyLength :
    Module.length R ((truncationQuotient K 1).homology 0) =
      Module.length R (K.homology 0) :=
  (truncationQuotientHomologyIso K 1 0 (by omega)).toLinearEquiv.length_eq.symm

/-- All positive-degree homology of that actual quotient vanishes. -/
theorem positiveQuotientExact (n : ℕ) : (truncationQuotient K 1).ExactAt (n + 1) :=
  truncationQuotient_exactAt K 1 n

/-- Repeated and zero equations preserve the actual canonical truncation sequence. -/
theorem repeatedZeroTruncationExact (a : R) (q : ℕ) :
    ((K.shortComplexTruncLE (chainPlacement q)).map
      (koszulTensorFunctor [a, a, 0])).ShortExact :=
  truncation_koszulTensor_shortExact K q [a, a, 0]

/-- The Euler decomposition at the first homology layer uses finiteness only
of the actual Koszul-tensored pieces. -/
theorem firstLayerTensorEuler (s : List R)
    (hT : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (K.truncLE (chainPlacement 1))))
    (hQ : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K 1))) :
    ∃ h : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) K),
      chainEuler (HomologicalComplex.tensorObj (chainComplex s) K) h =
        chainEuler (HomologicalComplex.tensorObj (chainComplex s)
          (K.truncLE (chainPlacement 1))) hT +
        chainEuler (HomologicalComplex.tensorObj (chainComplex s)
          (truncationQuotient K 1)) hQ :=
  ⟨truncation_koszulTensor_finiteHomology K 1 s hT hQ,
    truncation_koszulTensor_chainEuler K 1 s hT hQ⟩

end MotivicTest.KoszulHyperhomologyTruncation
