/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulHyperhomologyBounded
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.Algebra.Ring.Int.Field

/-!
# Positive-dimensional intermediate homology over the integers

The actual zero-multiplication complex on the integers has integer homology
in degrees zero and one, of infinite length. The later Koszul equation `2`
makes both coefficient complexes have finite homology. The bounded comparison
therefore applies to a genuine example excluded by finite-length intermediate
homology or finite-length chain-term assumptions.
-/

@[expose] public section

open CategoryTheory HomologicalComplex Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulHyperhomologyIntegers

/-- The coefficient ring in the concrete regression has positive dimension. -/
theorem dimensionOne : ringKrullDim ℤ = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

/-- Actual degree-zero homology of zero multiplication is the integer module. -/
noncomputable def homologyZeroIso :
    (singleComplex ℤ (0 : ℤ)).homology 0 ≅ ModuleCat.of ℤ ℤ :=
  singleHomologyZeroIso ℤ (0 : ℤ) ≪≫
    (Submodule.quotEquivOfEqBot (LinearMap.range (LinearMap.lsmul ℤ ℤ 0))
      (by simp)).toModuleIso

/-- Actual degree-one homology of zero multiplication is the integer module. -/
noncomputable def homologyOneIso :
    (singleComplex ℤ (0 : ℤ)).homology 1 ≅ ModuleCat.of ℤ ℤ :=
  singleHomologyOneIso ℤ (0 : ℤ) ≪≫
    (show LinearMap.ker (LinearMap.lsmul ℤ ℤ 0) ≃ₗ[ℤ] ℤ from
      { toFun := Subtype.val
        invFun := fun x => ⟨x, by simp⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toModuleIso

/-- The intermediate coefficient module has genuinely infinite length. -/
theorem integerLengthInfinite : Module.length ℤ ℤ = ⊤ := by
  by_contra h
  have hfinite := Module.length_ne_top_iff.mp h
  have : IsArtinianRing ℤ := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2
  exact Int.not_isField Ring.KrullDimLE.isField_of_isDomain

/-- The positive-degree homology of the actual first-stage complex has infinite length. -/
theorem positiveHomologyLengthInfinite :
    Module.length ℤ ((singleComplex ℤ (0 : ℤ)).homology 1) = ⊤ := by
  rw [homologyOneIso.toLinearEquiv.length_eq]
  exact integerLengthInfinite

/-- Degree-zero homology also has infinite length, so no surviving layer is
silently covered by a finite-length intermediate-homology assumption. -/
theorem zeroHomologyLengthInfinite :
    Module.length ℤ ((singleComplex ℤ (0 : ℤ)).homology 0) = ⊤ := by
  rw [homologyZeroIso.toLinearEquiv.length_eq]
  exact integerLengthInfinite

/-- Both original nonzero chain terms have infinite length. -/
theorem chainTermLengthInfinite (n : ℕ) (hn : n ≤ 1) :
    Module.length ℤ ((singleComplex ℤ (0 : ℤ)).X n) = ⊤ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact integerLengthInfinite
  · exact integerLengthInfinite

/-- The later equation gives a finite quotient, established by the actual `ZMod 2` equivalence. -/
theorem equationTwoArtinian : IsArtinianRing (ℤ ⧸ Ideal.ofList [(2 : ℤ)]) := by
  have : Finite (ℤ ⧸ Ideal.span {(2 : ℤ)}) :=
    Finite.of_equiv (ZMod 2) (Int.quotientSpanNatEquivZMod 2).symm.toEquiv
  rw [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq]
  infer_instance

/-- The actual later coefficient Koszul complex has finite homology. -/
theorem equationTwoFinite : FiniteHomology (coefficientComplex (ModuleCat.of ℤ ℤ) [2]) := by
  have : IsArtinianRing (ℤ ⧸ (Ideal.ofList [(2 : ℤ)] ⊔ (⊥ : Ideal ℤ))) := by
    rw [sup_bot_eq]
    exact equationTwoArtinian
  exact finiteHomology_of_artinian_quotient_of_le_annihilator
    (ModuleCat.of ℤ ℤ) [2] ⊥ bot_le

/-- Both surviving homology layers acquire finite homology after the later equation. -/
theorem layersFinite (n : ℕ) (hn : n ≤ 1) :
    FiniteHomology (coefficientComplex ((singleComplex ℤ (0 : ℤ)).homology n) [2]) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact equationTwoFinite.of_iso (fun j =>
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso
        ((coefficientFunctor [(2 : ℤ)]).mapIso homologyZeroIso)).symm)
  · exact equationTwoFinite.of_iso (fun j =>
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso
        ((coefficientFunctor [(2 : ℤ)]).mapIso homologyOneIso)).symm)

/-- Bounded hyperhomology gives actual signed cancellation despite infinite-length
intermediate homology and infinite-length original chain terms. -/
theorem signedInfiniteLengthCancellation :
    ∃ h : FiniteHomology (tensorObj (chainComplex [(2 : ℤ)]) (singleComplex ℤ (0 : ℤ))),
      chainEuler (tensorObj (chainComplex [(2 : ℤ)]) (singleComplex ℤ (0 : ℤ))) h = 0 := by
  have hBound : ∀ n, 1 < n → (singleComplex ℤ (0 : ℤ)).ExactAt n := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
    simpa only [Nat.add_comm] using singleExactAt_add_two ℤ (0 : ℤ) m
  obtain ⟨h, he⟩ := bounded_koszulTensor_chainEuler (singleComplex ℤ (0 : ℤ)) [2] 1
    hBound layersFinite
  refine ⟨h, ?_⟩
  have h0 : chainEuler (coefficientComplex ((singleComplex ℤ (0 : ℤ)).homology 0) [2])
      (layersFinite 0 (by omega)) =
      chainEuler (coefficientComplex (ModuleCat.of ℤ ℤ) [2]) equationTwoFinite :=
    homologyEuler_eq_of_quasiIso ((coefficientFunctor [2]).mapIso homologyZeroIso).hom
      _ _ _
  have h1 : chainEuler (coefficientComplex ((singleComplex ℤ (0 : ℤ)).homology 1) [2])
      (layersFinite 1 (by omega)) =
      chainEuler (coefficientComplex (ModuleCat.of ℤ ℤ) [2]) equationTwoFinite :=
    homologyEuler_eq_of_quasiIso ((coefficientFunctor [2]).mapIso homologyOneIso).hom
      _ _ _
  have he' : chainEuler (tensorObj (chainComplex [(2 : ℤ)]) (singleComplex ℤ (0 : ℤ))) h =
      chainEuler (coefficientComplex ((singleComplex ℤ (0 : ℤ)).homology 0) [2])
          (layersFinite 0 (by omega)) -
        chainEuler (coefficientComplex ((singleComplex ℤ (0 : ℤ)).homology 1) [2])
          (layersFinite 1 (by omega)) := by
    simpa [Fin.sum_univ_two, sub_eq_add_neg] using he
  rw [h0, h1, sub_self] at he'
  exact he'

end MotivicTest.KoszulHyperhomologyIntegers
