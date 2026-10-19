/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.SemilocalLengthDescent
public import Motivic.Aglib.Algebra.Homology.Koszul.ExteriorCoefficientComparison
public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyPlacement

/-!
# Generic maximal-localization finite-length descent consumers

The module theorem is consumed without a Noetherian ring or finite module.
A unit list contracts an arbitrary localized coefficient, while an empty
maximal spectrum tests the empty-index case of the general descent theorem.
Neither consumer supplies whole finite homology as an input.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u

namespace Motivic.MotivicTest.KoszulSemilocalLengthDescent

open _root_.HomologicalComplex.ModuleLengthEuler

/-- The generic module conclusion uses only actual maximal-localized lengths. -/
theorem actualModuleFiniteLength (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
    (M : ModuleCat.{u} R)
    (hlocal : ∀ q : MaximalSpectrum R,
      Module.length (Localization.AtPrime q.asIdeal)
        ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime q.asIdeal))).obj M) ≠ ⊤) :
    Module.length R M ≠ ⊤ :=
  length_ne_top_of_maximalLocalizations R M hlocal

/-- A unit contracts every actual localization of an arbitrary coefficient;
these constructed witnesses supply whole Koszul finite homology by descent. -/
theorem actualArbitraryCoefficientUnit (R : Type u) [CommRing R]
    [Finite (MaximalSpectrum R)] (M : ModuleCat.{u} R) :
    FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex M [1]) := by
  apply _root_.ChainComplex.Koszul.coefficient_finiteHomology_of_maximal R M [1]
  intro q
  let φ := algebraMap R (Localization.AtPrime q.asIdeal)
  let N := (ModuleCat.extendScalars φ).obj M
  have h : FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex N [1]) :=
    _root_.ChainComplex.Koszul.finiteHomology_of_identity_homotopy _
      (_root_.ChainComplex.Koszul.singleUnitTensorHomotopy ((ChainComplex.single₀ (ModuleCat _)).obj
          N))
  have hmap : FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex N ([1].map φ)) := by
    simpa only [List.map_cons, List.map_nil, map_one] using h
  exact hmap.of_iso (fun n => (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (_root_.ChainComplex.Koszul.coefficientExtendIso φ M [1]).symm)

/-- The empty maximal spectrum is included, with no nonempty-fiber assumption. -/
theorem actualEmptyMaximalSpectrum (R : Type u) [CommRing R]
    [IsEmpty (MaximalSpectrum R)] (M : ModuleCat.{u} R) (s : List R) :
    FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex M s) := by
  apply _root_.ChainComplex.Koszul.coefficient_finiteHomology_of_maximalLengths R M s
  intro q
  exact isEmptyElim q

end Motivic.MotivicTest.KoszulSemilocalLengthDescent
