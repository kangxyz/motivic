/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteProjection.Euler
public import Motivic.Aglib.RingTheory.Localization.FiniteFiberPoints

/-!
# Finite Koszul projection over an actual finite-morphism point fiber

The genuine localized finite algebra is A_p tensor_A B. Its established
maximal-point equivalence reindexes the actual Koszul Euler sum over all
source points above p. No single source stalk replaces the semilocal algebra.
-/

@[expose] public section

noncomputable section

universe u

open _root_.ChainComplex.Koszul
open _root_.HomologicalComplex.ModuleLengthEuler
open _root_.PrimeSpectrum.FiniteFiber

namespace MotivicTest.KoszulFiniteProjectionFiber

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] (p : PrimeSpectrum A) [IsNoetherianRing (Localization.AtPrime p.asIdeal)]

/-- The entire actual source point fiber indexes the residue-weighted Koszul sum,
with total finite homology required only over the genuine semilocal algebra. -/
theorem actualSourcePointProjection (s : List (Localization.AtPrime p.asIdeal))
    (K : ChainComplex (ModuleCat (localAlgebra A B p)) ℕ)
    (hK : FiniteHomology (finiteProjectionTotal (Localization.AtPrime p.asIdeal)
      (localAlgebra A B p) s K)) :
    chainEuler (finiteProjectionSource (Localization.AtPrime p.asIdeal) (localAlgebra A B p) s K)
        (finiteProjectionSource_finiteHomology (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) s K hK) =
      ∑ᶠ x : {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p},
        (Module.finiteAlgebraResidueDegree (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) ((maximalSpectrumEquivFiber A B p).symm x) : ℤ) *
        chainEuler (finiteProjectionLocal (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) s K ((maximalSpectrumEquivFiber A B p).symm x))
          (finiteProjectionLocal_finiteHomology (Localization.AtPrime p.asIdeal)
            (localAlgebra A B p) s K hK ((maximalSpectrumEquivFiber A B p).symm x)) := by
  rw [finiteProjection_chainEuler_finsum (Localization.AtPrime p.asIdeal)
    (localAlgebra A B p) s K hK]
  exact (finsum_comp_equiv (maximalSpectrumEquivFiber A B p).symm).symm

end MotivicTest.KoszulFiniteProjectionFiber
