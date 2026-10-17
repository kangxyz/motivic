/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.KoszulTorRegularBlockReduction

/-!
# Consumers of actual Tor regular-block reduction

The literal maps and arbitrary degree are retained, including a coefficient
image list equal to the singleton zero. No nontriviality assumption on the
composite quotient, flatness assumption, finite-length assumption, or
regularity assumption on the remaining coefficient equations is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Motivic

universe u

namespace MotivicTest.KoszulTorRegularBlockReduction

variable {R P Q C D : Type u}
  [CommRing R] [CommRing P] [CommRing Q] [CommRing C] [CommRing D]
  (f : R →+* P) (g : P →+* Q)
  (hf : Function.Surjective f) (hg : Function.Surjective g)
  (σ : R →+* C) (c : C →+* D)
  (hσ : Function.Surjective σ) (hc : Function.Surjective c)
  (t s : List R) (ht : RingTheory.Sequence.IsRegular R t)
  (hft : RingHom.ker f = Ideal.ofList t)
  (hs : RingTheory.Sequence.IsRegular P (s.map f))
  (hgs : RingHom.ker g = Ideal.ofList (s.map f))
  (hct : RingHom.ker c = Ideal.ofList (t.map σ))
  (hCt : RingTheory.Sequence.IsWeaklyRegular C (t.map σ)) (n : ℕ)

example :
    Module.length R
        (((Tor (ModuleCat R) n).obj
          ((ModuleCat.restrictScalars σ).obj (ModuleCat.of C C))).obj
            ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of Q Q))) =
      Module.length D
        ((Koszul.coefficientComplex (ModuleCat.of D D) ((s.map σ).map c)).homology n) :=
  Koszul.regularLeadingBlockTor_length f g hf hg σ c hσ hc t s ht hft hs hgs hct hCt n

example (hzero : (s.map σ).map c = [0]) :
    Module.length R
        (((Tor (ModuleCat R) n).obj
          ((ModuleCat.restrictScalars σ).obj (ModuleCat.of C C))).obj
            ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of Q Q))) =
      Module.length D
        ((Koszul.coefficientComplex (ModuleCat.of D D) [0]).homology n) := by
  rw [← hzero]
  exact Koszul.regularLeadingBlockTor_length f g hf hg σ c hσ hc t s ht hft hs hgs hct hCt n

end MotivicTest.KoszulTorRegularBlockReduction
