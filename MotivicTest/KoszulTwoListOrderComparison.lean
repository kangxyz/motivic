/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulTwoListOrderComparison

/-!
# Signed actual common-total consumers

The actual odd-odd tensor symmetry has a negative component sign. A zero
first equation has nonzero degree-one homology, of length one over a field.
Repeated/zero and empty lists exercise both fixed-support replacements,
with the swapped Artinian quotient always derived from the original ideal.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulTwoListOrderComparison

variable {R : Type u} [CommRing R]

/-- The exact signed symmetry used in the common total is negative on odd-odd
summands, not the unsigned flip of the underlying graded modules. -/
theorem oddOddBraiding (K L : ChainComplex (ModuleCat R) ℕ) :
    ιTensorObj K L 1 1 2 rfl ≫ (Motivic.TorComparison.tensorTotalSymmetryIso K L).hom.f 2 =
      -((β_ (K.X 1) (L.X 1)).hom ≫ ιTensorObj L K 1 1 2 rfl) := by
  simp only [Motivic.TorComparison.tensorTotalSymmetryIso, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_hom, ιTensorObj, ιMapBifunctor]
  erw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc]
  change (β_ (K.X 1) (L.X 1)).hom ≫
    (ιMapBifunctor K L (curriedTensor (ModuleCat R)).flip (ComplexShape.down ℕ) 1 1 2 rfl ≫
      (mapBifunctorFlipIso L K (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).hom.f 2) = _
  rw [ι_mapBifunctorFlipIso_hom]
  change (β_ (K.X 1) (L.X 1)).hom ≫
    (((-1 : ℤˣ) ^ (1 * 1 : ℕ)) • ιTensorObj L K 1 1 2 rfl) = _
  simp

/-- Actual order comparison works on unrestricted coefficient complexes. -/
def arbitraryComplexOrder (K : ChainComplex (ModuleCat R) ℕ) (a b : R) :
    HomologicalComplex.tensorObj (chainComplex [a, a, 0])
        (HomologicalComplex.tensorObj (chainComplex [b, 0]) K) ≅
      HomologicalComplex.tensorObj (chainComplex [b, 0])
        (HomologicalComplex.tensorObj (chainComplex [a, a, 0]) K) :=
  koszulTensorOrderIso K [a, a, 0] [b, 0]

/-- The repeated/zero coefficient comparison contains the actual differential square. -/
theorem repeatedDifferential (M : ModuleCat R) (a b : R) (i j : ℕ) :
    (twoListOrderIso M [a, a, 0] [b, 0]).hom.f i ≫
        (HomologicalComplex.tensorObj (chainComplex [b, 0])
          (coefficientComplex M [a, a, 0])).d i j =
      (HomologicalComplex.tensorObj (chainComplex [a, a, 0])
          (coefficientComplex M [b, 0])).d i j ≫
        (twoListOrderIso M [a, a, 0] [b, 0]).hom.f j :=
  twoListOrderIso_hom_comm M [a, a, 0] [b, 0] i j

/-- The actual first-stage positive homology of a zero equation is the ring module. -/
def zeroFirstStageHomologyOneIso :
    (coefficientComplex (ModuleCat.of R R) [0]).homology 1 ≅ ModuleCat.of R R :=
  (homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).mapIso
      (eqToIso (coefficientComplex_ring [0]) ≪≫ singletonIso 0) ≪≫
    singleHomologyOneIso R (0 : R) ≪≫
    (show LinearMap.ker (LinearMap.lsmul R R 0) ≃ₗ[R] R from
      { toFun := Subtype.val
        invFun := fun x => ⟨x, by simp⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toModuleIso

/-- The first-stage degree-one module is genuinely nonzero over a nonzero ring. -/
theorem zeroFirstStageHomologyOne_nonzero [Nontrivial R] :
    ¬ CategoryTheory.Limits.IsZero ((coefficientComplex (ModuleCat.of R R) [0]).homology 1) := by
  intro h
  have : Subsingleton R := ModuleCat.isZero_iff_subsingleton.mp
    (h.of_iso (zeroFirstStageHomologyOneIso (R := R)).symm)
  exact zero_ne_one (Subsingleton.elim (0 : R) 1)

/-- Over a field, the actual nonzero positive-degree first-stage length equals one. -/
theorem zeroFirstStageHomologyOne_length (k : Type u) [Field k] :
    Module.length k ((coefficientComplex (ModuleCat.of k k) [0]).homology 1) = 1 := by
  rw [(zeroFirstStageHomologyOneIso (R := k)).toLinearEquiv.length_eq]
  exact Module.length_eq_one k k

variable [IsNoetherianRing R]

/-- The generic first-stage coefficient really subtracts its degree-one length. -/
theorem firstStageGenericSign (M : ModuleCat R) [Module.Finite R M] (a : R)
    (p : (Ideal.ofList [a] ⊔ Module.annihilator R M).minimalPrimes) :
    twoListGenericEuler M [a] p =
      fixedSupportGenericLength ((coefficientComplex M [a]).homology 0)
          (Ideal.ofList [a] ⊔ Module.annihilator R M)
          (support_le_annihilator_coefficient_homology M [a] 0) p -
        fixedSupportGenericLength ((coefficientComplex M [a]).homology 1)
          (Ideal.ofList [a] ⊔ Module.annihilator R M)
          (support_le_annihilator_coefficient_homology M [a] 1) p := by
  simp [twoListGenericEuler, Fin.sum_univ_two, sub_eq_add_neg]

variable [IsLocalRing R]

/-- A repeated/zero first stage is replaced in either order with the same
actual coefficient, without assuming its homology vanishes in positive degrees. -/
theorem repeatedZeroFixedSupportOrder (M : ModuleCat R) [Module.Finite R M]
    (s : List R) (a : R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList [a, a, 0] ⊔ Module.annihilator R M)))]
    (hs : ∀ b ∈ s, b ∈ IsLocalRing.maximalIdeal R) (ha : a ∈ IsLocalRing.maximalIdeal R) :
    let := twoList_swappedArtinian M s [a, a, 0]
    twoListFixedSupportSum M s [a, a, 0] = twoListFixedSupportSum M [a, a, 0] s := by
  apply twoListFixedSupportSum_order M s [a, a, 0] hs
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ha
  · exact ha
  · exact Ideal.zero_mem _

/-- Empty later lists also identify the same two genuine support sums. -/
theorem emptyFixedSupportOrder (M : ModuleCat R) [Module.Finite R M] (t : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList [] ⊔
      (Ideal.ofList t ⊔ Module.annihilator R M)))]
    (ht : ∀ a ∈ t, a ∈ IsLocalRing.maximalIdeal R) :
    let := twoList_swappedArtinian M [] t
    twoListFixedSupportSum M [] t = twoListFixedSupportSum M t [] :=
  twoListFixedSupportSum_order M [] t (by simp) ht

end MotivicTest.KoszulTwoListOrderComparison
