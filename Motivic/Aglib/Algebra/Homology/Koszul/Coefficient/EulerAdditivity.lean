/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Coefficient.Functor
public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteSupport.Euler
public import Motivic.Aglib.Algebra.Homology.LengthEuler.Chain

/-!
# Euler additivity for arbitrary finite-list Koszul coefficients

The actual coefficient functor turns a coefficient short exact sequence into
one of complexes. The genuine homology long exact sequence then gives Euler
additivity. An Artinian quotient by the equations and any coefficient-annihilating
ideal supplies all finite-length and finite-support evidence. No regularity of
the equations or of the coefficient modules is required.
-/

@[expose] public section

universe u

open CategoryTheory
open _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- An Artinian equation quotient together with a coefficient-annihilating ideal
proves finite length in every degree and actual finite homology support. -/
theorem finiteHomology_of_artinian_quotient_of_le_annihilator [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (s : List R)
    (I : Ideal R) [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I))]
    (hI : I ≤ Module.annihilator R M) :
    FiniteHomology (coefficientComplex M s) where
  finite_length :=
    Module.KoszulFinite.length_homology_ne_top_of_artinian_quotient_of_le_annihilator
      M s I hI
  finite_support := (Finset.range (s.length + 1)).finite_toSet.subset
    (coefficient_homology_length_support_subset M s)

/-- Genuine arbitrary-list Koszul Euler length is additive in an actual short
exact coefficient sequence, without any scalar regularity hypothesis. -/
theorem coefficient_chainEuler_add_of_shortExact (s : List R)
    (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    (h₁ : FiniteHomology (coefficientComplex S.X₁ s))
    (h₂ : FiniteHomology (coefficientComplex S.X₂ s))
    (h₃ : FiniteHomology (coefficientComplex S.X₃ s)) :
    chainEuler (coefficientComplex S.X₂ s) h₂ =
      chainEuler (coefficientComplex S.X₁ s) h₁ +
        chainEuler (coefficientComplex S.X₃ s) h₃ :=
  chainEuler_add_of_shortExact (S.map (coefficientFunctor s))
    (coefficientFunctor_shortExact s S hS) h₁ h₂ h₃

/-- A common annihilating ideal on the middle coefficient module also
annihilates the submodule in a short exact sequence. -/
theorem annihilator_le_left_of_shortExact (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) : Module.annihilator R S.X₂ ≤ Module.annihilator R S.X₁ :=
  S.f.hom.annihilator_le_of_injective ((ModuleCat.mono_iff_injective _).mp hS.mono_f)

/-- A common annihilating ideal on the middle coefficient module also
annihilates the quotient in a short exact sequence. -/
theorem annihilator_le_right_of_shortExact (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) : Module.annihilator R S.X₂ ≤ Module.annihilator R S.X₃ :=
  S.g.hom.annihilator_le_of_surjective ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)

/-- Artinianness of a common equation-support quotient derives every finiteness
hypothesis in the arbitrary-list Euler additive law. -/
theorem coefficient_chainEuler_add_of_artinian_quotient [IsNoetherianRing R]
    (s : List R) (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (I : Ideal R) [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I))]
    (hI : I ≤ Module.annihilator R S.X₂) :
    chainEuler (coefficientComplex S.X₂ s)
        (finiteHomology_of_artinian_quotient_of_le_annihilator S.X₂ s I hI) =
      chainEuler (coefficientComplex S.X₁ s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator S.X₁ s I
            (hI.trans (annihilator_le_left_of_shortExact S hS))) +
        chainEuler (coefficientComplex S.X₃ s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator S.X₃ s I
            (hI.trans (annihilator_le_right_of_shortExact S hS))) :=
  coefficient_chainEuler_add_of_shortExact s S hS _ _ _

/-- The actual submodule sequence used for coefficient filtration steps. -/
noncomputable def coefficientSubmoduleSequence (M : ModuleCat R) (P : Submodule R M) :
    ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero P.subtype P.mkQ
    (LinearMap.exact_subtype_mkQ P).linearMap_comp_eq_zero

/-- The actual submodule inclusion and quotient map form a short exact sequence. -/
theorem coefficientSubmoduleSequence_shortExact (M : ModuleCat R) (P : Submodule R M) :
    (coefficientSubmoduleSequence M P).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ P)
    P.injective_subtype P.mkQ_surjective

/-- The arbitrary-list Euler law applies to every submodule filtration step,
with finite homology derived from an Artinian common support quotient. -/
theorem coefficient_chainEuler_add_submodule [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] (P : Submodule R M) (s : List R)
    (I : Ideal R) [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I))]
    (hI : I ≤ Module.annihilator R M) :
    chainEuler (coefficientComplex M s)
        (finiteHomology_of_artinian_quotient_of_le_annihilator M s I hI) =
      chainEuler (coefficientComplex (ModuleCat.of R P) s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator (ModuleCat.of R P) s I
            (hI.trans (P.subtype.annihilator_le_of_injective P.injective_subtype))) +
        chainEuler (coefficientComplex (ModuleCat.of R (M ⧸ P)) s)
          (finiteHomology_of_artinian_quotient_of_le_annihilator
            (ModuleCat.of R (M ⧸ P)) s I
            (hI.trans (P.mkQ.annihilator_le_of_surjective P.mkQ_surjective))) := by
  have : Module.Finite R (coefficientSubmoduleSequence M P).X₁ :=
    inferInstanceAs (Module.Finite R P)
  have : Module.Finite R (coefficientSubmoduleSequence M P).X₂ :=
    inferInstanceAs (Module.Finite R M)
  have : Module.Finite R (coefficientSubmoduleSequence M P).X₃ :=
    inferInstanceAs (Module.Finite R (M ⧸ P))
  exact coefficient_chainEuler_add_of_artinian_quotient s (coefficientSubmoduleSequence M P)
    (coefficientSubmoduleSequence_shortExact M P) I hI

end ChainComplex.Koszul
