/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulHyperhomologyTruncation
public import Motivic.Algebra.Homology.TorComparison.RegularQuotientBalance
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Actual projection to degree-zero homology under finite Koszul tensoring

The canonical projection of a nonnegative complex to its actual degree-zero
homology is a quasi-isomorphism whenever its positive homology vanishes.
Tensoring it with the actual finite Koszul complex preserves that comparison.
The resulting Euler equality needs finite homology only of the subsequent
coefficient Koszul complex, not finite length of the coefficient module.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex Motivic.LengthEuler

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat R) ℕ)

/-- The actual chain map from a nonnegative complex to its degree-zero homology. -/
noncomputable def degreeZeroProjection :
    K ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (K.homology 0) :=
  mkHomToSingle (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) (by
    intro i _
    rw [← Category.assoc, d_pOpcycles, zero_comp])

/-- On actual degree-zero homology, the canonical projection is the identity
under the single-complex homology isomorphism. -/
theorem degreeZeroProjection_homology :
    homologyMap (degreeZeroProjection K) 0 ≫
        (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (K.homology 0)).hom = 𝟙 _ := by
  apply (cancel_epi (K.homologyπ 0)).mp
  rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, ← Category.assoc, cyclesMap_i]
  simp only [degreeZeroProjection, mkHomToSingle_f, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← Category.assoc, ← K.homology_π_ι 0, Category.assoc]
  change K.homologyπ 0 ≫ (K.isoHomologyι₀.hom ≫ K.isoHomologyι₀.inv) = _
  simp

instance degreeZeroProjection_quasiIsoAt_zero : QuasiIsoAt (degreeZeroProjection K) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have he : homologyMap (degreeZeroProjection K) 0 =
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (K.homology 0)).inv := by
    apply (cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (K.homology 0)).hom).mp
    rw [degreeZeroProjection_homology, Iso.inv_hom_id]
  rw [he]
  infer_instance

/-- Vanishing of positive homology makes the actual degree-zero projection a quasi-isomorphism. -/
theorem degreeZeroProjection_quasiIso (hK : ∀ n, K.ExactAt (n + 1)) :
    QuasiIso (degreeZeroProjection K) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => infer_instance
  | succ n =>
    exact (quasiIsoAt_iff_exactAt (degreeZeroProjection K) (n + 1) (hK n)).mpr
      (exactAt_single_obj (ComplexShape.down ℕ) 0 (K.homology 0) (n + 1) (by omega))

/-- The actual cutoff-one quotient is quasi-isomorphic to its degree-zero homology. -/
theorem truncationQuotient_projection_quasiIso :
    QuasiIso (degreeZeroProjection (truncationQuotient K 1)) :=
  degreeZeroProjection_quasiIso _ (truncationQuotient_exactAt K 1)

/-- The actual Koszul-tensored projection, followed by the coefficient-tensor isomorphism. -/
noncomputable def degreeZeroTensorToCoefficient (s : List R) :
    HomologicalComplex.tensorObj (chainComplex s) K ⟶ coefficientComplex (K.homology 0) s :=
  (chainComplex s ◁ degreeZeroProjection K) ≫
    (Motivic.TorComparison.coefficientComplexTensorIso (K.homology 0) s).inv

/-- Finite K-flatness transports the actual degree-zero projection under Koszul tensoring. -/
theorem degreeZeroTensorToCoefficient_quasiIso (s : List R)
    (hK : ∀ n, K.ExactAt (n + 1)) : QuasiIso (degreeZeroTensorToCoefficient K s) := by
  have : QuasiIso (degreeZeroProjection K) := degreeZeroProjection_quasiIso K hK
  have : QuasiIso (chainComplex s ◁ degreeZeroProjection K) :=
    tensor_quasiIso (degreeZeroProjection K) s
  unfold degreeZeroTensorToCoefficient
  infer_instance

/-- Only the subsequent coefficient-Koszul homology must have finite length. -/
theorem degreeZeroTensor_finiteHomology (s : List R) (hK : ∀ n, K.ExactAt (n + 1))
    (hH : FiniteHomology (coefficientComplex (K.homology 0) s)) :
    FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) K) := by
  have : QuasiIso (degreeZeroTensorToCoefficient K s) :=
    degreeZeroTensorToCoefficient_quasiIso K s hK
  exact hH.of_iso (fun n => (isoOfQuasiIsoAt (degreeZeroTensorToCoefficient K s) n).symm)

/-- The true degree-zero hyperhomology Euler comparison, without finite length of `H₀(K)`. -/
theorem degreeZeroTensor_chainEuler (s : List R) (hK : ∀ n, K.ExactAt (n + 1))
    (hH : FiniteHomology (coefficientComplex (K.homology 0) s)) :
    chainEuler (HomologicalComplex.tensorObj (chainComplex s) K)
        (degreeZeroTensor_finiteHomology K s hK hH) =
      chainEuler (coefficientComplex (K.homology 0) s) hH := by
  have : QuasiIso (degreeZeroTensorToCoefficient K s) :=
    degreeZeroTensorToCoefficient_quasiIso K s hK
  exact homologyEuler_eq_of_quasiIso (degreeZeroTensorToCoefficient K s) _ _ hH

end Motivic.Koszul
