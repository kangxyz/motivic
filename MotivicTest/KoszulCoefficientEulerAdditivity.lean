/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Coefficient.EulerAdditivity

/-!
# Consumers of arbitrary-list coefficient Euler additivity

These tests use repeated and zero equations, actual submodule sequences,
and a square-ideal thickening. The square-ideal example applies the Euler law
to its actual ideal-generated layer; no regular sequence or split sequence is
assumed.
-/

@[expose] public section

universe u

open CategoryTheory _root_.ChainComplex.Koszul _root_.HomologicalComplex.ModuleLengthEuler

namespace MotivicTest.KoszulCoefficientEulerAdditivity

variable {R : Type u} [CommRing R]

/-- The new functor has literally the existing coefficient complex as object. -/
theorem actualObject (s : List R) (M : ModuleCat R) :
    (coefficientFunctor s).obj M = coefficientComplex M s := rfl

/-- Coefficient maps compose in a four-equation actual tensor complex. -/
theorem fourEquationComposition (a b c d : R) {M N P : ModuleCat R}
    (f : M ⟶ N) (g : N ⟶ P) :
    coefficientMap (f ≫ g) [a, b, c, d] =
      coefficientMap f [a, b, c, d] ≫ coefficientMap g [a, b, c, d] :=
  (coefficientFunctor [a, b, c, d]).map_comp f g

/-- Repetition and a zero equation do not obstruct exactness of coefficient sequences. -/
theorem repeatedZeroExact (a : R) (M : ModuleCat R) (P : Submodule R M) :
    ((coefficientSubmoduleSequence M P).map (coefficientFunctor [a, a, 0])).ShortExact :=
  coefficientFunctor_shortExact _ _ (coefficientSubmoduleSequence_shortExact M P)

/-- The actual square-ideal thickening used in the nonregular consumers. -/
abbrev squareQuotient (J : Ideal R) : ModuleCat R := ModuleCat.of R (R ⧸ J ^ 2)

/-- The ideal-generated layer inside the actual square-ideal thickening. -/
abbrev squareLayer (J : Ideal R) : Submodule R (squareQuotient J) :=
  J • (⊤ : Submodule R (squareQuotient J))

/-- The square ideal genuinely annihilates the square-ideal quotient. -/
theorem squareAnnihilator (J : Ideal R) :
    J ^ 2 ≤ Module.annihilator R (squareQuotient J) := by
  change J ^ 2 ≤ Module.annihilator R (R ⧸ J ^ 2)
  rw [Ideal.annihilator_quotient]

/-- Common support supplies genuine finite homology on an actual thickening. -/
theorem squareFiniteHomology [IsNoetherianRing R] (J : Ideal R) (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J ^ 2))] :
    FiniteHomology (coefficientComplex (squareQuotient J) s) :=
  finiteHomology_of_artinian_quotient_of_le_annihilator _ _ (J ^ 2) (squareAnnihilator J)

/-- The ideal-generated layer and its quotient have an actual short exact Koszul sequence. -/
theorem squareLayerExact (J : Ideal R) (s : List R) :
    ((coefficientSubmoduleSequence (squareQuotient J) (squareLayer J)).map
      (coefficientFunctor s)).ShortExact :=
  coefficientFunctor_shortExact _ _ (coefficientSubmoduleSequence_shortExact _ _)

/-- Genuine Euler additivity applies to the actual nilpotent-thickening layer,
with finite length derived from its equation-support quotient. -/
theorem squareLayerEuler [IsNoetherianRing R] (J : Ideal R) (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ J ^ 2))] :
    chainEuler (coefficientComplex (squareQuotient J) s) (squareFiniteHomology J s) =
      chainEuler (coefficientComplex (ModuleCat.of R (squareLayer J)) s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator _ s (J ^ 2)
            ((squareAnnihilator J).trans
              ((squareLayer J).subtype.annihilator_le_of_injective
                (squareLayer J).injective_subtype))) +
        chainEuler (coefficientComplex
            (ModuleCat.of R (squareQuotient J ⧸ squareLayer J)) s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator _ s (J ^ 2)
            ((squareAnnihilator J).trans
              ((squareLayer J).mkQ.annihilator_le_of_surjective
                (squareLayer J).mkQ_surjective))) :=
  coefficient_chainEuler_add_submodule _ _ _ (J ^ 2) (squareAnnihilator J)

/-- Repeated and zero equations still have their actual four-term finite range bound. -/
theorem repeatedZeroSupport (a : R) (M : ModuleCat R) :
    Function.support (fun n => Module.length R ((coefficientComplex M [a, a, 0]).homology n)) ⊆
      (Finset.range 4 : Set ℕ) :=
  coefficient_homology_length_support_subset M [a, a, 0]

end MotivicTest.KoszulCoefficientEulerAdditivity
