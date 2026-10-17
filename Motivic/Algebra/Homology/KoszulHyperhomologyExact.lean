/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulCoefficientFunctor
public import Motivic.Algebra.Homology.FiniteHomologyExact

/-!
# Exactness of actual finite Koszul tensoring on complexes

The actual ring Koszul tensor functor preserves short exact sequences of
nonnegative chain complexes. Finite-list induction uses the actual tensor
associator and the proved one-equation two-column exactness. Consequently,
finite homology and Euler additivity require finiteness only after tensoring
both outer complexes, not finite-length homology of the original complexes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Motivic.LengthEuler

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]

/-- Tensoring an arbitrary nonnegative complex with the actual finite ring Koszul complex. -/
noncomputable def koszulTensorFunctor (s : List R) :
    ChainComplex (ModuleCat R) ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
  tensorLeft (chainComplex s)

instance instKoszulTensorFunctorAdditive (s : List R) : (koszulTensorFunctor s).Additive := by
  induction s with
  | nil =>
    exact Functor.additive_of_iso (leftUnitorNatIso (ChainComplex (ModuleCat R) ℕ)).symm
  | cons a s ih =>
    have : (koszulTensorFunctor s).Additive := ih
    exact Functor.additive_of_iso
      (show koszulTensorFunctor s ⋙ singleTensorFunctor a ≅ koszulTensorFunctor (a :: s) from
        (tensorLeftTensor (singleComplex R a) (chainComplex s)).symm)

/-- Finite Koszul tensoring preserves actual short exact sequences of complexes. -/
theorem koszulTensor_shortExact (s : List R)
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact) :
    (S.map (koszulTensorFunctor s)).ShortExact := by
  induction s with
  | nil =>
    exact ShortComplex.shortExact_of_iso
      (S.mapNatIso (show koszulTensorFunctor ([] : List R) ≅ 𝟭 _ from
        leftUnitorNatIso (ChainComplex (ModuleCat R) ℕ))).symm hS
  | cons a s ih =>
    exact ShortComplex.shortExact_of_iso
      (S.mapNatIso (show koszulTensorFunctor (a :: s) ≅
        koszulTensorFunctor s ⋙ singleTensorFunctor a from
          tensorLeftTensor (singleComplex R a) (chainComplex s))).symm
      (singleTensor_shortExact a (S.map (koszulTensorFunctor s)) ih)

/-- Only finite homology after Koszul tensoring is needed for the middle complex. -/
theorem koszulTensor_finiteHomology_middle (s : List R)
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact)
    (hA : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) S.X₁))
    (hC : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) S.X₃)) :
    FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) S.X₂) :=
  FiniteHomology.shortExact_middle (S.map (koszulTensorFunctor s))
    (koszulTensor_shortExact s S hS) hA hC

/-- The Euler law on an actual short exact sequence asks for no finite length
of the original complexes' homology. -/
theorem koszulTensor_chainEuler_add (s : List R)
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact)
    (hA : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) S.X₁))
    (hC : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) S.X₃)) :
    chainEuler (HomologicalComplex.tensorObj (chainComplex s) S.X₂)
        (koszulTensor_finiteHomology_middle s S hS hA hC) =
      chainEuler (HomologicalComplex.tensorObj (chainComplex s) S.X₁) hA +
        chainEuler (HomologicalComplex.tensorObj (chainComplex s) S.X₃) hC :=
  chainEuler_add_of_shortExact_outer (S.map (koszulTensorFunctor s))
    (koszulTensor_shortExact s S hS) hA hC

end Motivic.Koszul
