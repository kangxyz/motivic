/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyExact
public import Motivic.Aglib.Algebra.Homology.Koszul.DimensionCancellation
public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteSupport.Basic

/-!
# Koszul Euler length of an actually placed complex

The scalar-one column sequence relates an arbitrary complex to its actual
degree-one placement. The middle complex is explicitly contractible, even
after tensoring with another finite Koszul complex. Applying the exact tensor
functor to this real short exact sequence therefore derives finiteness and
the negative Euler sign of the placed tensor from finiteness of the original
tensor. No finite-length assumption on the original untensored homology is
made, and no tensor-placement isomorphism is assumed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat R) ℕ)

/-- The actual scalar-one tensor is explicitly contractible. -/
noncomputable def singleUnitTensorHomotopy :
    Homotopy (𝟙 (tensorObj (singleComplex R 1) K)) 0 := by
  have h : Homotopy ((1 : R) • 𝟙 (tensorObj (singleComplex R 1) K)) 0 :=
    (Homotopy.ofEq (tensorHom_scalar_left (singleComplex R 1) K 1).symm).trans
      ((mapBifunctorMapHomotopy₁ (singleScalarHomotopy R 1)
        (𝟙 K) (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ)).trans
        (Homotopy.ofEq (tensorHom_zero_left (singleComplex R 1) K)))
  simpa only [one_smul] using h

/-- The scalar-one tensor remains explicitly contractible under the actual finite Koszul tensor. -/
noncomputable def koszulUnitTensorHomotopy (s : List R) :
    Homotopy (𝟙 (tensorObj (chainComplex s) (tensorObj (singleComplex R 1) K))) 0 := by
  have h := (mapBifunctorMapHomotopy₂ (𝟙 (chainComplex s)) (singleUnitTensorHomotopy K)
    (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).trans
    (Homotopy.ofEq (tensorHom_zero_right (chainComplex s) (tensorObj (singleComplex R 1) K)))
  have hid : tensorHom (𝟙 (chainComplex s)) (𝟙 (tensorObj (singleComplex R 1) K)) =
      𝟙 (tensorObj (chainComplex s) (tensorObj (singleComplex R 1) K)) := by
    simpa only [one_smul] using
      tensorHom_scalar_right (chainComplex s) (tensorObj (singleComplex R 1) K) (1 : R)
  exact (Homotopy.ofEq hid.symm).trans h

/-- A null-homotopic identity gives genuine zero homology in each degree. -/
theorem isZero_homology_of_identity_homotopy (h : Homotopy (𝟙 K) 0) (n : ℕ) :
    IsZero (K.homology n) := by
  rw [IsZero.iff_id_eq_zero]
  simpa only [homologyMap_id, homologyMap_zero] using h.homologyMap_eq n

/-- A contractible complex has actual finite homology, without assumptions on its terms. -/
theorem finiteHomology_of_identity_homotopy (h : Homotopy (𝟙 K) 0) : FiniteHomology K :=
  FiniteLengthSupport.of_isZero_outside _ ∅ (by simp)
    (fun n _ => isZero_homology_of_identity_homotopy K h n)

/-- The Euler length of an actually contractible complex is zero. -/
theorem chainEuler_of_identity_homotopy (h : Homotopy (𝟙 K) 0) (hK : FiniteHomology K) :
    chainEuler K hK = 0 := by
  change (∑ᶠ n, (-1 : ℤ) ^ n * integerLength (K.homology n) (hK.finite_length n)) = 0
  have hz : ∀ n, (-1 : ℤ) ^ n * integerLength (K.homology n) (hK.finite_length n) = 0 := by
    intro n
    have : Subsingleton (K.homology n) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_homology_of_identity_homotopy K h n)
    simp [integerLength]
  simp only [hz, finsum_zero]

/-- Finiteness after tensoring survives actual degree-one placement. -/
theorem koszulTensor_placement_finiteHomology (s : List R)
    (hK : FiniteHomology (tensorObj (chainComplex s) K)) :
    FiniteHomology (tensorObj (chainComplex s) (K.extend (chainPlacement 1))) :=
  FiniteHomology.shortExact_right
    ((koszulDimensionColumnSequence (1 : R) K).map (koszulTensorFunctor s))
    (koszulTensor_shortExact s _ (koszulDimensionColumnSequence_shortExact 1 K)) hK
    (finiteHomology_of_identity_homotopy _ (koszulUnitTensorHomotopy K s))

/-- The actual degree-one placed Koszul tensor contributes the negative Euler length. -/
theorem koszulTensor_placement_chainEuler (s : List R)
    (hK : FiniteHomology (tensorObj (chainComplex s) K)) :
    chainEuler (tensorObj (chainComplex s) (K.extend (chainPlacement 1)))
        (koszulTensor_placement_finiteHomology K s hK) =
      -chainEuler (tensorObj (chainComplex s) K) hK := by
  have he := chainEuler_add_of_shortExact
    ((koszulDimensionColumnSequence (1 : R) K).map (koszulTensorFunctor s))
    (koszulTensor_shortExact s _ (koszulDimensionColumnSequence_shortExact 1 K)) hK
    (finiteHomology_of_identity_homotopy _ (koszulUnitTensorHomotopy K s))
    (koszulTensor_placement_finiteHomology K s hK)
  change chainEuler (tensorObj (chainComplex s) (tensorObj (singleComplex R 1) K)) _ =
    chainEuler (tensorObj (chainComplex s) K) hK +
      chainEuler (tensorObj (chainComplex s) (K.extend (chainPlacement 1))) _ at he
  have hz := chainEuler_of_identity_homotopy
    (tensorObj (chainComplex s) (tensorObj (singleComplex R 1) K))
    (koszulUnitTensorHomotopy K s)
    (finiteHomology_of_identity_homotopy _ (koszulUnitTensorHomotopy K s))
  omega

end ChainComplex.Koszul
