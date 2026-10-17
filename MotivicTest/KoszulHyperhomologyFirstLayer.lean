/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulHyperhomologyFirstLayer
public import Motivic.Algebra.Homology.KoszulCoefficientEulerAdditivity

/-!
# Actual first-layer coefficient homology comparisons

These consumers check the literal degree-zero projection and the true
Koszul-tensored quotient comparison. An Artinian equation-support quotient
supplies finite length only after applying the subsequent Koszul complex.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulHyperhomologyFirstLayer

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat R) ℕ)

/-- The actual degree-zero component is the canonical quotient to homology. -/
theorem projectionZeroComponent :
    (degreeZeroProjection K).f 0 = K.pOpcycles 0 ≫ K.isoHomologyι₀.inv := by
  simp [degreeZeroProjection, mkHomToSingle_f]

/-- Repetition and a zero equation preserve the actual first-layer quasi-isomorphism. -/
theorem repeatedZeroFirstLayerComparison (a : R) :
    QuasiIso (firstQuotientTensorToCoefficient K [a, a, 0]) := inferInstance

/-- The actual quotient tensor has finite homology as soon as the coefficient
Koszul homology does, with no assumption on finite length of `H₀(K)`. -/
theorem firstLayerFinite (s : List R)
    (hH : FiniteHomology (coefficientComplex (K.homology 0) s)) :
    FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) (truncationQuotient K 1)) :=
  firstQuotientTensor_finiteHomology K s hH

/-- Artinian support gives the genuine degree-zero comparison for a complex
whose positive homology vanishes, without assuming finite length of `H₀(K)`. -/
theorem supportedDegreeZeroEuler [IsNoetherianRing R]
    [Module.Finite R (K.homology 0)] (s : List R) (I : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I))]
    (hI : I ≤ Module.annihilator R (K.homology 0))
    (hK : ∀ n, K.ExactAt (n + 1)) :
    ∃ h : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) K),
      chainEuler (HomologicalComplex.tensorObj (chainComplex s) K) h =
        chainEuler (coefficientComplex (K.homology 0) s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator (K.homology 0) s I hI) :=
  ⟨degreeZeroTensor_finiteHomology K s hK
      (finiteHomology_of_artinian_quotient_of_le_annihilator (K.homology 0) s I hI),
    degreeZeroTensor_chainEuler K s hK _⟩

/-- The actual first-layer Euler contribution is obtained from the original
homology coefficient, while all higher homology remains unrestricted. -/
theorem supportedFirstTruncationEuler [IsNoetherianRing R]
    [Module.Finite R (K.homology 0)] (s : List R) (I : Ideal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I))]
    (hI : I ≤ Module.annihilator R (K.homology 0))
    (hT : FiniteHomology
      (HomologicalComplex.tensorObj (chainComplex s) (K.truncLE (chainPlacement 1)))) :
    ∃ h : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) K),
      chainEuler (HomologicalComplex.tensorObj (chainComplex s) K) h =
        chainEuler (HomologicalComplex.tensorObj (chainComplex s)
          (K.truncLE (chainPlacement 1))) hT +
        chainEuler (coefficientComplex (K.homology 0) s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator (K.homology 0) s I hI) :=
  firstTruncation_chainEuler K s hT _

end MotivicTest.KoszulHyperhomologyFirstLayer
