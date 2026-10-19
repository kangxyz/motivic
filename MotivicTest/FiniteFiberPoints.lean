/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Localization.FiniteFiberPoints
public import Motivic.Aglib.Algebra.Homology.LengthEuler.FiniteAlgebra

/-!
# Source-point consumers of the finite-algebra Euler formula

The actual point equivalence reindexes the full Euler sum over the geometric
point fiber. The hypotheses concern finite homology over the entire localized
algebra, without finite-length terms or finiteness of individual source stalks.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace Motivic.MotivicTest.FiniteFiberPoints

open _root_.PrimeSpectrum.FiniteFiber _root_.HomologicalComplex.ModuleLengthEuler

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] (p : PrimeSpectrum A) [IsNoetherianRing (Localization.AtPrime p.asIdeal)]

/-- The Euler formula may be indexed by all actual source points over the target prime. -/
theorem chainEuler_source_point_sum
    [Fintype {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p}]
    (K : ChainComplex (ModuleCat.{u} (localAlgebra A B p)) ℕ) (hK : FiniteHomology K) :
    chainEuler (finiteAlgebraRestrictedComplex (Localization.AtPrime p.asIdeal)
        (localAlgebra A B p) K)
        (hK.finiteAlgebra_restrict (Localization.AtPrime p.asIdeal) (localAlgebra A B p) K) =
      ∑ x : {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p},
        (Module.finiteAlgebraResidueDegree (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) ((maximalSpectrumEquivFiber A B p).symm x) : ℤ) *
        chainEuler (finiteAlgebraLocalizedComplex (localAlgebra A B p) K
          ((maximalSpectrumEquivFiber A B p).symm x))
          (hK.finiteAlgebra_localized (Localization.AtPrime p.asIdeal) (localAlgebra A B p) K
            ((maximalSpectrumEquivFiber A B p).symm x)) := by
  have := Module.finiteAlgebra_maximalSpectrum_finite
    (Localization.AtPrime p.asIdeal) (localAlgebra A B p)
  let : Fintype (MaximalSpectrum (localAlgebra A B p)) := Fintype.ofFinite _
  rw [chainEuler_finiteAlgebra (Localization.AtPrime p.asIdeal) (localAlgebra A B p) K hK]
  exact ((maximalSpectrumEquivFiber A B p).symm.sum_comp _).symm

omit [IsNoetherianRing (Localization.AtPrime p.asIdeal)] in
/-- The fiber enumeration is derived from finiteness, rather than an extra geometric assumption. -/
theorem finite_source_points :
    Finite {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p} :=
  pointFiber_finite A B p

omit [IsNoetherianRing (Localization.AtPrime p.asIdeal)] in
/-- Distinct source points remain distinct maximal branches of the semilocal algebra. -/
theorem distinct_branches
    {x y : {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p}} (h : x ≠ y) :
    (maximalSpectrumEquivFiber A B p).symm x ≠ (maximalSpectrumEquivFiber A B p).symm y :=
  (maximalSpectrumEquivFiber A B p).symm.injective.ne h

end Motivic.MotivicTest.FiniteFiberPoints
