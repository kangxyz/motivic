/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulHyperhomologyExact
public import Motivic.Algebra.Homology.LengthEulerExtendChain
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# Actual truncation sequences under finite Koszul tensoring

The canonical truncation retaining homology in degrees at least `q` is a
subcomplex, and its actual cokernel has the original homology in degrees
below `q` and zero homology in degrees at least `q`. Its short exact sequence
remains short exact after finite Koszul tensoring. Euler additivity then
uses finite homology only of the two tensored pieces, without any
finite-length hypothesis on the original complex's homology.
-/

@[expose] public section

universe u

open CategoryTheory Motivic.LengthEuler

namespace Motivic.LengthEuler

instance instChainPlacementIsTruncLE (q : ℕ) : (chainPlacement q).IsTruncLE where
  mem_prev := by
    intro i j h
    change (j + q) + 1 = i at h
    refine ⟨j + 1, ?_⟩
    change (j + 1) + q = i
    omega

end Motivic.LengthEuler

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat R) ℕ) (q : ℕ)

/-- The actual cokernel of the canonical subcomplex retaining homology at and above `q`. -/
noncomputable def truncationQuotient : ChainComplex (ModuleCat R) ℕ :=
  (K.shortComplexTruncLE (chainPlacement q)).X₃

/-- The actual truncation quotient has zero homology at and above its cutoff. -/
theorem truncationQuotient_exactAt (n : ℕ) :
    (truncationQuotient K q).ExactAt (n + q) :=
  (K.shortComplexTruncLE_X₃_isSupportedOutside (chainPlacement q)).exactAt n

/-- Below the cutoff, the canonical quotient map gives the actual homology isomorphism. -/
noncomputable def truncationQuotientHomologyIso (n : ℕ) (hn : n < q) :
    K.homology n ≅ (truncationQuotient K q).homology n := by
  have : QuasiIsoAt (K.shortComplexTruncLE (chainPlacement q)).g n :=
    K.quasiIsoAt_shortComplexTruncLE_g (chainPlacement q) n (by
      intro i
      change i + q ≠ n
      omega)
  exact isoOfQuasiIsoAt (K.shortComplexTruncLE (chainPlacement q)).g n

/-- The canonical truncation short exact sequence remains actual short exact after tensoring. -/
theorem truncation_koszulTensor_shortExact (s : List R) :
    ((K.shortComplexTruncLE (chainPlacement q)).map (koszulTensorFunctor s)).ShortExact :=
  koszulTensor_shortExact s _ (K.shortComplexTruncLE_shortExact (chainPlacement q))

/-- Finiteness of the two tensored truncation pieces suffices for finiteness of the total tensor. -/
theorem truncation_koszulTensor_finiteHomology (s : List R)
    (hT : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (K.truncLE (chainPlacement q))))
    (hQ : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K q))) :
    FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) K) :=
  koszulTensor_finiteHomology_middle s (K.shortComplexTruncLE (chainPlacement q))
    (K.shortComplexTruncLE_shortExact (chainPlacement q)) hT hQ

/-- Euler additivity for a genuine tensored canonical truncation sequence. -/
theorem truncation_koszulTensor_chainEuler (s : List R)
    (hT : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (K.truncLE (chainPlacement q))))
    (hQ : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K q))) :
    chainEuler (HomologicalComplex.tensorObj (chainComplex s) K)
        (truncation_koszulTensor_finiteHomology K q s hT hQ) =
      chainEuler (HomologicalComplex.tensorObj (chainComplex s)
        (K.truncLE (chainPlacement q))) hT +
      chainEuler (HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K q)) hQ :=
  koszulTensor_chainEuler_add s (K.shortComplexTruncLE (chainPlacement q))
    (K.shortComplexTruncLE_shortExact (chainPlacement q)) hT hQ

end Motivic.Koszul
