/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteSupportEuler
public import Motivic.Algebra.Homology.LengthEulerFiniteAlgebra
public import Mathlib.Data.DFinsupp.WellFounded

/-!
# Finite Koszul homology from every maximal localization

This public, geometry-independent boundary exposes the maximal-localization
finite-length criterion used privately in `FinitePushforwardLengthDescent`.
Its proof retains the same order-reflecting map of submodule lattices.
A finite maximal spectrum yields both chain conditions; no decomposition of
the ring or module into a product of localizations is asserted.

Flat localization compares actual homology. A coefficient Koszul complex's
finite list supplies its degree bound, so local finite lengths give whole
finite homology without Noetherianity or finite coefficient or term modules.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

universe u

namespace Motivic

/-- Categorical and tensor localizations retain the same canonical ring structure. -/
local instance semilocalLengthLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- Scalar maps use the same canonical localization semiring. -/
local instance semilocalLengthLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

namespace LengthEuler

private def maximalSubmoduleEmbedding (S : Type u) [CommRing S] (M : ModuleCat.{u} S) :
    Submodule S M ↪o ∀ q : MaximalSpectrum S,
      Submodule (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⊗[S] M) := by
  let g := fun (N : Submodule S M) (q : MaximalSpectrum S) =>
    N.localized' (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
      (TensorProduct.mk S (Localization.AtPrime q.asIdeal) M 1)
  refine OrderEmbedding.ofMapLEIff g ?_
  intro N N'
  constructor
  · intro h
    apply Submodule.le_of_localization_maximal
      (fun P _ => Localization.AtPrime P ⊗[S] M)
      (fun P _ => TensorProduct.mk S (Localization.AtPrime P) M 1)
    intro P hP
    exact h ⟨P, hP⟩
  · intro h q
    exact (Submodule.localized'gi (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
      (TensorProduct.mk S (Localization.AtPrime q.asIdeal) M 1)).gc.monotone_l h

/-- Over any commutative ring with finitely many maximal ideals, finite lengths
at all actual maximal localizations imply finite length of the original module.
No Noetherian ring or finite-generation hypothesis is required. -/
theorem length_ne_top_of_maximalLocalizations (S : Type u) [CommRing S]
    [Finite (MaximalSpectrum S)] (M : ModuleCat.{u} S)
    (hM : ∀ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        ((ModuleCat.extendScalars (algebraMap S (Localization.AtPrime q.asIdeal))).obj M) ≠ ⊤) :
    Module.length S M ≠ ⊤ := by
  have hfin (q : MaximalSpectrum S) : IsFiniteLength (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[S] M) := by
    apply Module.length_ne_top_iff.mp
    rw [← (finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime q.asIdeal) M).length_eq]
    exact hM q
  let Q := fun q : MaximalSpectrum S =>
    Submodule (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⊗[S] M)
  have : ∀ q : MaximalSpectrum S, WellFoundedLT (Q q) := fun q =>
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hfin q)).2
  have : ∀ q : MaximalSpectrum S, WellFoundedGT (Q q) := fun q =>
    isNoetherian_iff.mp (isFiniteLength_iff_isNoetherian_isArtinian.mp (hfin q)).1
  let e := maximalSubmoduleEmbedding S M
  have : IsArtinian S M := e.wellFoundedLT
  let ed : (Submodule S M)ᵒᵈ ↪o ∀ q, (Q q)ᵒᵈ :=
    OrderEmbedding.ofMapLEIff (fun N q => e N q) (fun _ _ => e.le_iff_le)
  have : IsNoetherian S M := isNoetherian_iff.mpr ed.wellFoundedLT
  exact Module.length_ne_top

end LengthEuler

namespace Koszul

open LengthEuler

variable (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
  (M : ModuleCat.{u} R) (s : List R)

/-- Actual finite homology lengths at all maximal localizations descend to the
whole coefficient Koszul complex. The literal list bounds its degree support. -/
theorem coefficient_finiteHomology_of_maximalLengths
    (hlocal : ∀ (q : MaximalSpectrum R) (n : ℕ),
      Module.length (Localization.AtPrime q.asIdeal)
        ((finiteAlgebraLocalizedComplex R (coefficientComplex M s) q).homology n) ≠ ⊤) :
    FiniteHomology (coefficientComplex M s) where
  finite_length n := by
    apply length_ne_top_of_maximalLocalizations R ((coefficientComplex M s).homology n)
    intro q
    rw [← (finiteAlgebraLocalizedHomologyIso R
      (coefficientComplex M s) q n).toLinearEquiv.length_eq]
    exact hlocal q n
  finite_support := (Finset.range (s.length + 1)).finite_toSet.subset
    (coefficient_homology_length_support_subset M s)

/-- Finite homology of every actual maximal-localized Koszul complex supplies
all local lengths needed for whole finite homology, with no common bound input. -/
theorem coefficient_finiteHomology_of_maximal
    (hlocal : ∀ q : MaximalSpectrum R,
      FiniteHomology (finiteAlgebraLocalizedComplex R (coefficientComplex M s) q)) :
    FiniteHomology (coefficientComplex M s) :=
  coefficient_finiteHomology_of_maximalLengths R M s (fun q => (hlocal q).finite_length)

end Koszul

end Motivic
