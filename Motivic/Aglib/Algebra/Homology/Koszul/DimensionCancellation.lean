/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Coefficient.EulerAdditivity
public import Motivic.Aglib.Algebra.Homology.LengthEuler.ExtendChain
public import Motivic.Aglib.Algebra.Homology.FiniteSupport.ShortExact

/-!
# Euler cancellation in the actual two-column Koszul tensor

The old-column inclusion and the signed new-column projection give a genuine
short exact sequence from a complex through its one-equation Koszul tensor
to its extension by zero in degree one. The alternating sign corrects the
negative differential on the new column. For finite homology, genuine Euler
additivity and the degree shift prove cancellation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R) (K : ChainComplex (ModuleCat.{u} R) ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual old-column inclusion into the one-equation tensor complex. -/
noncomputable def koszulDimensionOldColumn :
    K ⟶ HomologicalComplex.tensorObj (singleComplex R a) K where
  f n := singleTensorιZero a K n
  comm' i j h := by
    have hij : j + 1 = i := h
    subst i
    exact singleTensorιZero_d a K j

set_option backward.isDefEq.respectTransparency false in
/-- The signed projection from the new column to the unsigned degree-one
placement. The degree-dependent sign corrects the tensor differential. -/
noncomputable def koszulDimensionNewColumn :
    HomologicalComplex.tensorObj (singleComplex R a) K ⟶ K.extend (chainPlacement 1) where
  f
    | 0 => 0
    | n + 1 => ((-1 : ℤ) ^ n) •
        (singleTensorπOne a K n ≫ (K.extendXIso (chainPlacement 1) (i' := n + 1) (i := n) rfl).inv)
  comm' i j h := by
    have hij : j + 1 = i := h
    subst i
    cases j with
    | zero =>
      exact (K.isZero_extend_X (chainPlacement 1) 0 (by
        intro n
        simp [chainPlacement])).eq_of_tgt _ _
    | succ n =>
      dsimp only
      erw [K.extend_d_eq (chainPlacement 1) (i' := n + 2) (j' := n + 1)
        (i := n + 1) (j := n) rfl rfl]
      simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
        Iso.inv_hom_id_assoc, pow_succ, mul_neg_one, neg_smul, Preadditive.neg_comp]
      have hd := congrArg (fun f => ((-1 : ℤ) ^ n) •
        (f ≫ (K.extendXIso (chainPlacement 1) (i' := n + 1) (i := n) rfl).inv))
        (singleTensor_d_πOne a K n)
      simpa only [Category.assoc, Preadditive.neg_comp, smul_neg] using! hd.symm

set_option backward.isDefEq.respectTransparency false in
/-- The old and new column maps form the actual short complex. -/
noncomputable def koszulDimensionColumnSequence :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (koszulDimensionOldColumn a K) (koszulDimensionNewColumn a K) (by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => exact comp_zero
    | succ n =>
      change singleTensorιZero a K (n + 1) ≫
        (((-1 : ℤ) ^ n) • (singleTensorπOne a K n ≫ _)) = 0
      simp [← Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/-- Every actual degreewise column sequence is split exact; the splitting is
only degreewise and is not asserted to commute with the differential. -/
noncomputable def koszulDimensionColumnSplitting (n : ℕ) :
    ((koszulDimensionColumnSequence a K).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).Splitting where
  r := singleTensorπZero a K n
  s := by
    cases n with
    | zero => exact 0
    | succ n => exact ((-1 : ℤ) ^ n) •
        ((K.extendXIso (chainPlacement 1) (i' := n + 1) (i := n) rfl).hom ≫
          singleTensorιOne a K n)
  f_r := by
    exact singleTensorιZero_πZero a K n
  s_g := by
    cases n with
    | zero =>
      exact (K.isZero_extend_X (chainPlacement 1) 0 (by
        intro n
        simp [chainPlacement])).eq_of_src _ _
    | succ n =>
      change (((-1 : ℤ) ^ n) • (_ ≫ singleTensorιOne a K n)) ≫
        (((-1 : ℤ) ^ n) • (singleTensorπOne a K n ≫ _)) = 𝟙 _
      simp [Category.assoc, smul_smul, ← mul_pow]
  id := by
    cases n with
    | zero =>
      change singleTensorπZero a K 0 ≫ singleTensorιZero a K 0 + 0 =
        𝟙 ((HomologicalComplex.tensorObj (singleComplex R a) K).X 0)
      simp
    | succ n =>
      change singleTensorπZero a K (n + 1) ≫ singleTensorιZero a K (n + 1) +
        (((-1 : ℤ) ^ n) • (singleTensorπOne a K n ≫ _)) ≫
          (((-1 : ℤ) ^ n) • (_ ≫ singleTensorιOne a K n)) = 𝟙 _
      simpa [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
        smul_smul, ← mul_pow] using singleTensor_decomposition a K n

/-- The actual two-column Koszul sequence is short exact in the category of
nonnegative chain complexes. -/
theorem koszulDimensionColumnSequence_shortExact :
    (koszulDimensionColumnSequence a K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (koszulDimensionColumnSplitting a K n).shortExact

/-- Finite homology of the tail implies finite homology of its actual
one-equation Koszul tensor. -/
theorem koszulDimensionTensor_finiteHomology (hK : FiniteHomology K) :
    FiniteHomology (HomologicalComplex.tensorObj (singleComplex R a) K) :=
  FiniteHomology.shortExact_middle (koszulDimensionColumnSequence a K)
    (koszulDimensionColumnSequence_shortExact a K) hK (hK.extend (chainPlacement 1))

/-- The genuine Euler length of a one-equation tensor with finite homology
vanishes, for every scalar. No finite length of the complex terms is assumed. -/
theorem koszulDimensionTensor_chainEuler_zero (hK : FiniteHomology K) :
    chainEuler (HomologicalComplex.tensorObj (singleComplex R a) K)
      (koszulDimensionTensor_finiteHomology a K hK) = 0 := by
  have he := chainEuler_add_of_shortExact_outer (koszulDimensionColumnSequence a K)
    (koszulDimensionColumnSequence_shortExact a K) hK (hK.extend (chainPlacement 1))
  change chainEuler (HomologicalComplex.tensorObj (singleComplex R a) K) _ =
    chainEuler K hK + chainEuler (K.extend (chainPlacement 1)) _ at he
  rw [chainEuler_extend_placement K 1 hK] at he
  simpa using he

end ChainComplex.Koszul
