/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulRegularBlockElimination
public import Motivic.Algebra.Homology.KoszulFlatLocalMultiplicity
public import Motivic.RingTheory.RegularSequence.SurjectiveComposition

/-!
# Actual Tor after eliminating a regular leading coefficient block

Two successive regular kernels give the literal appended Koszul resolution of
the composite quotient. After applying a surjective coefficient action, only
the weakly regular leading block is eliminated. The remaining equation list is
its image under the specified maps, in every homological degree. Neither
flatness of a quotient map nor regularity of the remaining coefficient list nor
finite length is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Motivic.Koszul

variable {R P Q C D : Type u}
  [CommRing R] [CommRing P] [CommRing Q] [CommRing C] [CommRing D]

/-- Actual Tor against a composite regular-kernel quotient has the length of
the remaining Koszul homology over the actual coefficient quotient. -/
theorem regularLeadingBlockTor_length
    (f : R →+* P) (g : P →+* Q)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (σ : R →+* C) (c : C →+* D)
    (hσ : Function.Surjective σ) (hc : Function.Surjective c)
    (t s : List R) (ht : RingTheory.Sequence.IsRegular R t)
    (hft : RingHom.ker f = Ideal.ofList t)
    (hs : RingTheory.Sequence.IsRegular P (s.map f))
    (hgs : RingHom.ker g = Ideal.ofList (s.map f))
    (hct : RingHom.ker c = Ideal.ofList (t.map σ))
    (hCt : RingTheory.Sequence.IsWeaklyRegular C (t.map σ)) (n : ℕ) :
    Module.length R
        (((Tor (ModuleCat R) n).obj
          ((ModuleCat.restrictScalars σ).obj (ModuleCat.of C C))).obj
            ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of Q Q))) =
      Module.length D
        ((coefficientComplex (ModuleCat.of D D) ((s.map σ).map c)).homology n) := by
  have : Nontrivial Q := by
    refine nontrivial_of_ne (1 : Q) 0 ?_
    intro h
    apply hs.top_ne_smul
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← hgs]
    exact ((Ideal.eq_top_iff_one _).mpr
      (show g 1 = 0 by simpa only [map_one] using h)).symm
  obtain ⟨hts, hcomp⟩ :=
    RegularSequence.isRegular_append_of_surjective_kernel f g hf t s ht hft hs hgs
  let M := (ModuleCat.restrictScalars σ).obj (ModuleCat.of C C)
  let e :
      ((Tor (ModuleCat R) n).obj M).obj
          ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of Q Q)) ≅
        (coefficientComplex M (t ++ s)).homology n :=
    ((Tor (ModuleCat R) n).obj M).mapIso
        (regularBlockQuotientIso (g.comp f) (hg.comp hf) (t ++ s) hcomp).symm ≪≫
      finiteTorIsoHomology M (t ++ s) hts.toIsWeaklyRegular n
  calc
    _ = Module.length R ((coefficientComplex M (t ++ s)).homology n) :=
      e.toLinearEquiv.length_eq
    _ = Module.length C
        ((coefficientComplex (ModuleCat.of C C) ((t ++ s).map σ)).homology n) :=
      coordinateHomology_length σ hσ (t ++ s) n
    _ = _ := by
      rw [List.map_append]
      exact regularBlockHomology_length c hc (t.map σ) (s.map σ) hct hCt n

end Motivic.Koszul
