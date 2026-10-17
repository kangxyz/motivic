/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardResidueDegree
public import MotivicTest.KoszulFiniteProjectionFiber

/-!
# Actual scheme residue weights in the finite Koszul fiber formula

The source-point reindexing now carries the literal scheme residue degrees.
Only the total complex over the whole localized finite algebra is assumed to
have finite homology. Identifying that complex with a given geometric
coefficient complex remains a separate comparison.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Motivic.Koszul Motivic.LengthEuler Motivic.FiniteFiber

universe u

namespace Motivic.MotivicTest.FinitePushforwardResidueDegree

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B] (p : PrimeSpectrum A)

/-- The numerical weight is the actual scheme residue degree at every source point above p. -/
theorem actualSourceWeight
    (x : {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p}) :
    LocalLength.finiteAlgebraResidueDegree (Localization.AtPrime p.asIdeal)
        (localAlgebra A B p) ((maximalSpectrumEquivFiber A B p).symm x) =
      (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree x.1 := by
  rw [finiteAlgebraResidueDegree_eq_schemeResidueDegree A B p]
  have hx := congrArg Subtype.val ((maximalSpectrumEquivFiber A B p).apply_symm_apply x)
  exact congrArg (fun y =>
    (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree y) hx

variable [IsNoetherianRing (Localization.AtPrime p.asIdeal)]

/-- The whole finite Koszul source fiber has precisely the scheme-pushforward residue weights. -/
theorem schemeWeightedSourcePointProjection (s : List (Localization.AtPrime p.asIdeal))
    (K : ChainComplex (ModuleCat.{u} (localAlgebra A B p)) ℕ)
    (hK : FiniteHomology (finiteProjectionTotal (Localization.AtPrime p.asIdeal)
      (localAlgebra A B p) s K)) :
    chainEuler (finiteProjectionSource (Localization.AtPrime p.asIdeal) (localAlgebra A B p) s K)
        (finiteProjectionSource_finiteHomology (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) s K hK) =
      ∑ᶠ x : {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p},
        ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree x.1 : ℤ) *
        chainEuler (finiteProjectionLocal (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) s K ((maximalSpectrumEquivFiber A B p).symm x))
          (finiteProjectionLocal_finiteHomology (Localization.AtPrime p.asIdeal)
            (localAlgebra A B p) s K hK ((maximalSpectrumEquivFiber A B p).symm x)) := by
  rw [MotivicTest.KoszulFiniteProjectionFiber.actualSourcePointProjection A B p s K hK]
  apply finsum_congr
  intro x
  rw [actualSourceWeight A B p x]

end Motivic.MotivicTest.FinitePushforwardResidueDegree
