/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteSupport.Euler

/-!
# Consumers of arbitrary finite Koszul support and Euler finiteness

These checks include lists with repeated and zero equations, all-zero lists
of arbitrary length over a field, local minimal coefficient support, and genuine
Tor of an Artinian regular-sequence quotient with itself. In the last example
the defining equations annihilate the coefficient module, so no coefficient
regularity is smuggled into the Tor or finiteness statements.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.ChainComplex.Koszul _root_.HomologicalComplex.ModuleLengthEuler

namespace Motivic.MotivicTest.KoszulFiniteSupport

variable {R : Type u} [CommRing R]

example (M : ModuleCat R) (a b : R) :
    Homotopy (a • 𝟙 (coefficientComplex M [a, 0, a, b])) 0 :=
  coefficientScalarHomotopy M [a, 0, a, b] a (by simp)

example (M : ModuleCat R) (s : List R) (n : ℕ) :
    Ideal.ofList s ⊔ Module.annihilator R M ≤
      Module.annihilator R ((coefficientComplex M s).homology n) :=
  support_le_annihilator_coefficient_homology M s n

example [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat R) [Module.Finite R M]
    (s : List R) (hm : IsLocalRing.maximalIdeal R ∈
      (Ideal.ofList s ⊔ Module.annihilator R M).minimalPrimes) :
    FiniteHomology (coefficientComplex M s) :=
  finiteHomology_of_mem_minimalPrimes_support M s hm

/-- Every all-zero list, of arbitrary length, has genuine finite homology over a field. -/
theorem finiteHomology_zeroList (k : Type u) [Field k] (M : ModuleCat k)
    [Module.Finite k M] (d : ℕ) :
    FiniteHomology (coefficientComplex M (List.replicate d 0)) :=
  finiteHomology_of_artinian_support_quotient M (List.replicate d 0)

/-- An Artinian cyclic coefficient support suffices for every all-zero list,
even when the ambient ring and its zero-equation quotient are not Artinian. -/
theorem finiteHomology_zeroList_cyclic [IsNoetherianRing R]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (d : ℕ) :
    FiniteHomology (coefficientComplex (ModuleCat.of R (R ⧸ I)) (List.replicate d 0)) := by
  have hz : Ideal.ofList (List.replicate d (0 : R)) = ⊥ := by
    induction d with
    | zero => simp
    | succ d ih => simp [List.replicate_succ, ih]
  have : IsArtinianRing (R ⧸ (Ideal.ofList (List.replicate d (0 : R)) ⊔
      Module.annihilator R (ModuleCat.of R (R ⧸ I)))) := by
    change IsArtinianRing (R ⧸ (Ideal.ofList (List.replicate d (0 : R)) ⊔
      Module.annihilator R (R ⧸ I)))
    rw [hz, Ideal.annihilator_quotient, bot_sup_eq]
    infer_instance
  exact finiteHomology_of_artinian_support_quotient
    (ModuleCat.of R (R ⧸ I)) (List.replicate d 0)

/-- The Artinian regular-sequence quotient has genuine finite self-Tor support. -/
theorem finiteLengthSupport_selfTor [IsNoetherianRing R] (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) [IsArtinianRing (R ⧸ Ideal.ofList s)] :
    FiniteLengthSupport (fun n =>
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))).obj
        (ModuleCat.of R (R ⧸ Ideal.ofList s))) := by
  have : IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      Module.annihilator R (ModuleCat.of R (R ⧸ Ideal.ofList s)))) := by
    change IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R (R ⧸ Ideal.ofList s)))
    rw [Ideal.annihilator_quotient, sup_idem]
    infer_instance
  exact finiteLengthSupport_finiteTor_of_artinian_support_quotient
    (ModuleCat.of R (R ⧸ Ideal.ofList s)) s hs

end Motivic.MotivicTest.KoszulFiniteSupport
