/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulDimensionZeroHead
public import Motivic.Algebra.Homology.KoszulDimensionSupport

/-!
# Consumers of actual Koszul dimension-induction steps

The tests exercise both prime-quotient branches: a head in the prime gives
actual Euler zero, while a head outside the prime is proved regular and gives
a real quasi-isomorphism to quotient coefficients. The local dimension drop
and Artinian support propagation are checked on those actual coefficients.
No complete prime-filtration dimension-vanishing theorem is asserted here.
-/

@[expose] public section

universe u

open CategoryTheory Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulDimensionSteps

variable {R : Type u} [CommRing R]

/-- The general two-column exact sequence does not require a zero or regular
scalar; its degreewise signed splitting supplies actual exactness. -/
theorem arbitraryScalarColumns (a : R) (K : ChainComplex (ModuleCat R) ℕ) :
    (koszulDimensionColumnSequence a K).ShortExact :=
  koszulDimensionColumnSequence_shortExact a K

/-- Arbitrary finite homology, rather than finite-length terms, suffices for
Euler cancellation in the actual two-column tensor. -/
theorem arbitraryScalarCancellation (a : R) (K : ChainComplex (ModuleCat R) ℕ)
    (hK : FiniteHomology K) :
    chainEuler (HomologicalComplex.tensorObj (singleComplex R a) K)
      (koszulDimensionTensor_finiteHomology a K hK) = 0 :=
  koszulDimensionTensor_chainEuler_zero a K hK

/-- The head-in-prime branch gives genuine Euler zero for an arbitrary tail. -/
theorem primeZeroHead [IsNoetherianRing R] (p : Ideal R) (a : R) (s : List R)
    (ha : a ∈ p) [IsArtinianRing (R ⧸ (Ideal.ofList (a :: s) ⊔ p))] :
    ∃ h : FiniteHomology (coefficientComplex (ModuleCat.of R (R ⧸ p)) (a :: s)),
      chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p)) (a :: s)) h = 0 := by
  have : IsArtinianRing (R ⧸
      (Ideal.ofList (a :: s) ⊔ Module.annihilator R (ModuleCat.of R (R ⧸ p)))) := by
    change IsArtinianRing (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R (R ⧸ p)))
    rw [Ideal.annihilator_quotient]
    infer_instance
  refine ⟨finiteHomology_of_artinian_support_quotient _ _, ?_⟩
  apply koszulDimension_chainEuler_zero_of_mem_annihilator
  change a ∈ Module.annihilator R (R ⧸ p)
  rwa [Ideal.annihilator_quotient]

/-- Domain regularity of a nonzero prime-quotient scalar gives the actual
regular-head quasi-isomorphism; no tail regularity is assumed. -/
theorem primeRegularHead (p : Ideal R) [p.IsPrime] (a : R) (s : List R)
    (ha : a ∉ p) : QuasiIso (koszulDimensionReduction (ModuleCat.of R (R ⧸ p)) a s) :=
  koszulDimensionReduction_quasiIso _ _ _ (Motivic.LocalLength.scalar_regular_primeQuotient p a ha)

/-- The strict dimension bound survives passing to literal quotient
coefficients in the regular prime-quotient branch. -/
theorem primeDimensionDrop [IsNoetherianRing R] [IsLocalRing R]
    (p : Ideal R) [p.IsPrime] (a : R) (s : List R) (ha : a ∉ p)
    (hm : a ∈ IsLocalRing.maximalIdeal R)
    (hd : Module.supportDim R (R ⧸ p) < (a :: s).length) :
    Module.supportDim R ((scalarQuotientFunctor a).obj (ModuleCat.of R (R ⧸ p))) < s.length :=
  koszulDimensionReduction_supportDim_lt _ _ _
    (Motivic.LocalLength.scalar_regular_primeQuotient p a ha) hm hd

/-- The tail's actual quotient coefficients retain the required Artinian
support hypothesis, even before regularity is used. -/
theorem quotientSupport [IsNoetherianRing R] (M : ModuleCat R) (a : R) (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R M))] :
    IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      Module.annihilator R ((scalarQuotientFunctor a).obj M))) :=
  koszulDimension_artinian_scalarQuotient M a s

end MotivicTest.KoszulDimensionSteps
