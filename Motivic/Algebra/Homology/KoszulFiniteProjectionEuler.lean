/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteProjectionExtension
public import Motivic.Algebra.Homology.LengthEulerFiniteAlgebra

/-!
# Residue-weighted finite projection for actual Koszul tensors

For a finite algebra over a Noetherian local base, finite homology of the
actual target-algebra Koszul tensor implies finite homology of the restricted
base-ring Koszul tensor and of every actual maximal-point localized Koszul
tensor. Their Euler characteristics satisfy the residue-degree weighted sum.
Neither the finite algebra nor the original complex is assumed flat, and the
original complex need not have finite homology or finite-length terms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace Motivic.Koszul

open LengthEuler

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The literal target-algebra Koszul tensor before restriction or localization. -/
abbrev finiteProjectionTotal (s : List R) (K : ChainComplex (ModuleCat S) ℕ) :=
  HomologicalComplex.tensorObj (chainComplex (s.map (algebraMap R S))) K

/-- The literal base-ring Koszul tensor with the restricted original complex. -/
abbrev finiteProjectionSource (s : List R) (K : ChainComplex (ModuleCat S) ℕ) :=
  HomologicalComplex.tensorObj (chainComplex s) (finiteAlgebraRestrictedComplex R S K)

/-- The actual localized Koszul tensor at a maximal point, retaining the
composite image of every equation and the genuine localized coefficient complex. -/
abbrev finiteProjectionLocal (s : List R) (K : ChainComplex (ModuleCat S) ℕ)
    (p : MaximalSpectrum S) :=
  HomologicalComplex.tensorObj
    (chainComplex ((s.map (algebraMap R S)).map
      (algebraMap S (Localization.AtPrime p.asIdeal))))
    (finiteAlgebraLocalizedComplex S K p)

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R S]

/-- Finite homology of the actual target total complex implies finite homology
of the base Koszul tensor; no finite-homology premise on the original complex is used. -/
theorem finiteProjectionSource_finiteHomology (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) (hK : FiniteHomology (finiteProjectionTotal R S s K)) :
    FiniteHomology (finiteProjectionSource R S s K) :=
  (hK.finiteAlgebra_restrict R S (finiteProjectionTotal R S s K)).of_quasiIso
    (koszulTensorRestrictIso (algebraMap R S) s K).hom

omit [IsLocalRing R] in
/-- Every maximal-point local Koszul total has genuine finite homology, derived
from the total S-homology and the actual localization chain comparison. -/
theorem finiteProjectionLocal_finiteHomology (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) (hK : FiniteHomology (finiteProjectionTotal R S s K))
    (p : MaximalSpectrum S) : FiniteHomology (finiteProjectionLocal R S s K p) :=
  (hK.finiteAlgebra_localized R S (finiteProjectionTotal R S s K) p).of_quasiIso
    (koszulTensorExtendIso (algebraMap S (Localization.AtPrime p.asIdeal))
      (s.map (algebraMap R S)) K).hom

/-- Finite-list Koszul projection sums all maximal branches with their actual
finite residue degrees. Every Euler term uses derived finite-homology evidence. -/
theorem finiteProjection_chainEuler [Fintype (MaximalSpectrum S)] (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) (hK : FiniteHomology (finiteProjectionTotal R S s K)) :
    chainEuler (finiteProjectionSource R S s K)
        (finiteProjectionSource_finiteHomology R S s K hK) =
      ∑ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        chainEuler (finiteProjectionLocal R S s K p)
          (finiteProjectionLocal_finiteHomology R S s K hK p) := by
  calc
    _ = chainEuler (finiteAlgebraRestrictedComplex R S (finiteProjectionTotal R S s K))
        (hK.finiteAlgebra_restrict R S (finiteProjectionTotal R S s K)) :=
      (homologyEuler_eq_of_quasiIso (koszulTensorRestrictIso (algebraMap R S) s K).hom
        (fun n => (-1) ^ n) (hK.finiteAlgebra_restrict R S (finiteProjectionTotal R S s K))
        (finiteProjectionSource_finiteHomology R S s K hK)).symm
    _ = ∑ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        chainEuler (finiteAlgebraLocalizedComplex S (finiteProjectionTotal R S s K) p)
          (hK.finiteAlgebra_localized R S (finiteProjectionTotal R S s K) p) :=
      chainEuler_finiteAlgebra R S (finiteProjectionTotal R S s K) hK
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      exact homologyEuler_eq_of_quasiIso
        (koszulTensorExtendIso (algebraMap S (Localization.AtPrime p.asIdeal))
          (s.map (algebraMap R S)) K).hom (fun n => (-1) ^ n)
        (hK.finiteAlgebra_localized R S (finiteProjectionTotal R S s K) p)
        (finiteProjectionLocal_finiteHomology R S s K hK p)

/-- The canonical weighted formula derives the finite maximal-point index set
from the actual finite algebra; no enumeration or semilocality is assumed. -/
theorem finiteProjection_chainEuler_finsum (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) (hK : FiniteHomology (finiteProjectionTotal R S s K)) :
    chainEuler (finiteProjectionSource R S s K)
        (finiteProjectionSource_finiteHomology R S s K hK) =
      ∑ᶠ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        chainEuler (finiteProjectionLocal R S s K p)
          (finiteProjectionLocal_finiteHomology R S s K hK p) := by
  let : Finite (MaximalSpectrum S) := Module.finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact finiteProjection_chainEuler R S s K hK

end Motivic.Koszul
