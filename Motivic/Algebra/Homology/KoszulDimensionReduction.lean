/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulCoefficientEulerAdditivity
public import Motivic.Algebra.Homology.KoszulCoefficientRegularity
public import Motivic.Algebra.Homology.KoszulSingleTensorQuotient
public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Regular-head reduction for dimension induction on Koszul Euler length

If the first equation acts injectively on the coefficient module, the actual
tensor augmentation followed by the actual coefficient-quotient comparison
is a quasi-isomorphism to the tail Koszul complex with quotient coefficients.
It therefore preserves the genuine finite-length Euler characteristic.

Over a Noetherian local ring the literal coefficient quotient has the expected
support-dimension drop when the head lies in the maximal ideal. These are
proved induction steps, not a claim of the full dimension-vanishing theorem.
-/

@[expose] public section

universe u

open CategoryTheory Motivic.LengthEuler

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]

/-- The actual regular-head comparison map has the tail complex with literal
scalar-quotient coefficients as its target. -/
noncomputable def koszulDimensionReduction (M : ModuleCat R) (a : R) (s : List R) :
    coefficientComplex M (a :: s) ⟶
      coefficientComplex ((scalarQuotientFunctor a).obj M) s :=
  tensorAugmentation a (coefficientComplex M s) ≫ (coefficientQuotientIso a M s).hom

set_option backward.isDefEq.respectTransparency false in
/-- Regularity on the coefficient module makes the actual regular-head map a
quasi-isomorphism, without regularity of any tail equation. -/
theorem koszulDimensionReduction_quasiIso (M : ModuleCat R) (a : R) (s : List R)
    (ha : IsSMulRegular M a) : QuasiIso (koszulDimensionReduction M a s) := by
  have : QuasiIso (tensorAugmentation a (coefficientComplex M s)) :=
    tensorAugmentation_quasiIso_of_regular a (coefficientComplex M s)
      (coefficientComplex_isSMulRegular M s a ha)
  dsimp only [koszulDimensionReduction]
  infer_instance

/-- Finite homology passes through the actual regular-head comparison. -/
theorem koszulDimensionReduction_finiteHomology (M : ModuleCat R) (a : R) (s : List R)
    (ha : IsSMulRegular M a) (h : FiniteHomology (coefficientComplex M (a :: s))) :
    FiniteHomology (coefficientComplex ((scalarQuotientFunctor a).obj M) s) := by
  have := koszulDimensionReduction_quasiIso M a s ha
  exact h.of_quasiIso (koszulDimensionReduction M a s)

/-- The regular-head reduction preserves the genuine Euler characteristic of
all homology degrees, not just degree zero. -/
theorem koszulDimensionReduction_chainEuler (M : ModuleCat R) (a : R) (s : List R)
    (ha : IsSMulRegular M a) (h : FiniteHomology (coefficientComplex M (a :: s))) :
    chainEuler (coefficientComplex M (a :: s)) h =
      chainEuler (coefficientComplex ((scalarQuotientFunctor a).obj M) s)
        (koszulDimensionReduction_finiteHomology M a s ha h) := by
  have := koszulDimensionReduction_quasiIso M a s ha
  exact homologyEuler_eq_of_quasiIso (koszulDimensionReduction M a s) _ _ _

/-- The Artinian coefficient-support hypothesis supplies all finite homology
required by regular-head Euler reduction. -/
theorem koszulDimensionReduction_chainEuler_of_artinian_support [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (a : R) (s : List R)
    (ha : IsSMulRegular M a)
    [IsArtinianRing (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R M))] :
    chainEuler (coefficientComplex M (a :: s))
        (finiteHomology_of_artinian_support_quotient M (a :: s)) =
      chainEuler (coefficientComplex ((scalarQuotientFunctor a).obj M) s)
        (koszulDimensionReduction_finiteHomology M a s ha
          (finiteHomology_of_artinian_support_quotient M (a :: s))) :=
  koszulDimensionReduction_chainEuler M a s ha _

/-- The literal scalar-quotient coefficients satisfy the local support-dimension
formula. The maximal-ideal premise is explicit. -/
theorem koszulDimensionReduction_supportDim [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat R) [Module.Finite R M] (a : R)
    (ha : IsSMulRegular M a) (hm : a ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R ((scalarQuotientFunctor a).obj M) + 1 = Module.supportDim R M := by
  change Module.supportDim R (SingleQuotient M a) + 1 = Module.supportDim R M
  rw [Module.supportDim_eq_of_equiv (singleQuotientEquivQuotSMulTop M a)]
  exact Module.supportDim_quotSMulTop_succ_eq_supportDim ha hm

/-- Strict dimension smaller than the whole list becomes strict dimension
smaller than the tail after the actual regular-head reduction. -/
theorem koszulDimensionReduction_supportDim_lt [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat R) [Module.Finite R M] (a : R) (s : List R)
    (ha : IsSMulRegular M a) (hm : a ∈ IsLocalRing.maximalIdeal R)
    (hd : Module.supportDim R M < (a :: s).length) :
    Module.supportDim R ((scalarQuotientFunctor a).obj M) < s.length := by
  apply ENat.WithBot.add_one_le_natCast_iff.mp
  rw [koszulDimensionReduction_supportDim M a ha hm]
  exact ENat.WithBot.lt_add_one_iff.mp (by simpa using hd)

end Motivic.Koszul
