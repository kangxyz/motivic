/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.LengthEulerFiniteAlgebraModules
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.Additive

/-!
# The finite-algebra fiber formula for actual homology Euler characteristics

Exact restriction of scalars and flat localization compare the homology of
actual mapped complexes with the actual restricted or localized homology
modules. Thus finite homology over a finite algebra over a Noetherian local
base implies finite homology after restriction and at every maximal point.
The integer Euler characteristic over the base is the sum of the localized
Euler characteristics weighted by their actual finite residue degrees.

No flatness of the finite algebra, surjectivity of its structure map, or
Artinian hypothesis on it is assumed. The numerical formula is derived from
the actual module-length theorem, rather than supplied as comparison data.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace Motivic.LengthEuler

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type v} {c : ComplexShape ι}

/-- The literal restriction of the modules and differentials of a complex. -/
abbrev finiteAlgebraRestrictedComplex (K : HomologicalComplex (ModuleCat.{u} S) c) :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex c).obj K

/-- The literal localization of all modules and differentials at a maximal point. -/
abbrev finiteAlgebraLocalizedComplex (K : HomologicalComplex (ModuleCat.{u} S) c)
    (p : MaximalSpectrum S) :=
  ((ModuleCat.extendScalars
    (algebraMap S (Localization.AtPrime p.asIdeal))).mapHomologicalComplex c).obj K

/-- Exact restriction identifies actual homology for an arbitrary algebra map. -/
def finiteAlgebraRestrictHomologyIso (K : HomologicalComplex (ModuleCat.{u} S) c) (i : ι) :
    (finiteAlgebraRestrictedComplex R S K).homology i ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap R S))

/-- Flat localization identifies the actual localized homology with the
homology of the actual localized complex, including its local scalar action. -/
def finiteAlgebraLocalizedHomologyIso (K : HomologicalComplex (ModuleCat.{u} S) c)
    (p : MaximalSpectrum S) (i : ι) :
    (finiteAlgebraLocalizedComplex S K p).homology i ≅
      (ModuleCat.extendScalars (algebraMap S (Localization.AtPrime p.asIdeal))).obj
        (K.homology i) := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat S (Localization.AtPrime p.asIdeal)))
  exact (K.sc i).mapHomologyIso
    (ModuleCat.extendScalars (algebraMap S (Localization.AtPrime p.asIdeal)))

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R S]

/-- Genuine finite homology survives restriction along a finite algebra. -/
theorem FiniteHomology.finiteAlgebra_restrict
    (K : HomologicalComplex (ModuleCat.{u} S) c) (hK : FiniteHomology K) :
    FiniteHomology (finiteAlgebraRestrictedComplex R S K) :=
  (FiniteLengthSupport.finiteAlgebra_restrict R S (fun i => K.homology i) hK).of_iso
    (fun i => (finiteAlgebraRestrictHomologyIso R S K i).symm)

include R in
omit [IsLocalRing R] in
/-- Genuine finite homology survives localization at every maximal point. -/
theorem FiniteHomology.finiteAlgebra_localized
    (K : HomologicalComplex (ModuleCat.{u} S) c) (hK : FiniteHomology K)
    (p : MaximalSpectrum S) : FiniteHomology (finiteAlgebraLocalizedComplex S K p) :=
  (FiniteLengthSupport.finiteAlgebra_localized R S (fun i => K.homology i) hK p).of_iso
    (fun i => (finiteAlgebraLocalizedHomologyIso S K p i).symm)

/-- The finite-algebra all-point Euler formula for any common integer sign function. -/
theorem homologyEuler_finiteAlgebra [Fintype (MaximalSpectrum S)]
    (K : HomologicalComplex (ModuleCat.{u} S) c) (sign : ι → ℤ) (hK : FiniteHomology K) :
    homologyEuler (finiteAlgebraRestrictedComplex R S K) sign
        (FiniteHomology.finiteAlgebra_restrict R S K hK) =
      ∑ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        homologyEuler (finiteAlgebraLocalizedComplex S K p) sign
          (FiniteHomology.finiteAlgebra_localized R S K hK p) := by
  unfold homologyEuler
  rw [signedLengthSum_eq_of_iso sign _
    (FiniteLengthSupport.finiteAlgebra_restrict R S (fun i => K.homology i) hK)
    (finiteAlgebraRestrictHomologyIso R S K)]
  rw [signedLengthSum_finiteAlgebra R S (fun i => K.homology i) sign hK]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  exact signedLengthSum_eq_of_iso sign _ _
    (fun i => (finiteAlgebraLocalizedHomologyIso S K p i).symm)

/-- The all-point sum uses the finite maximal spectrum derived from the algebra. -/
def finiteAlgebraFiberEuler (K : HomologicalComplex (ModuleCat.{u} S) c)
    (sign : ι → ℤ) (hK : FiniteHomology K) : ℤ :=
  let : Finite (MaximalSpectrum S) := Module.finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  ∑ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
    homologyEuler (finiteAlgebraLocalizedComplex S K p) sign
      (FiniteHomology.finiteAlgebra_localized R S K hK p)

/-- The canonical fiber Euler formula needs no separately assumed enumeration,
semilocality, residue finiteness, or local homology finiteness. -/
theorem homologyEuler_finiteAlgebra_eq_fiberEuler
    (K : HomologicalComplex (ModuleCat.{u} S) c) (sign : ι → ℤ) (hK : FiniteHomology K) :
    homologyEuler (finiteAlgebraRestrictedComplex R S K) sign
        (FiniteHomology.finiteAlgebra_restrict R S K hK) =
      finiteAlgebraFiberEuler R S K sign hK := by
  let : Finite (MaximalSpectrum S) := Module.finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  exact homologyEuler_finiteAlgebra R S K sign hK

/-- In particular the usual alternating chain Euler characteristic satisfies
the actual weighted finite-pushforward fiber formula. -/
theorem chainEuler_finiteAlgebra [Fintype (MaximalSpectrum S)]
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (hK : FiniteHomology K) :
    chainEuler (finiteAlgebraRestrictedComplex R S K)
        (FiniteHomology.finiteAlgebra_restrict R S K hK) =
      ∑ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        chainEuler (finiteAlgebraLocalizedComplex S K p)
          (FiniteHomology.finiteAlgebra_localized R S K hK p) :=
  homologyEuler_finiteAlgebra R S K (fun i => (-1) ^ i) hK

end Motivic.LengthEuler
