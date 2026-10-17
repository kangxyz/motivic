/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulRegularBlockElimination

/-!
# Consumers of actual regular-block elimination

All degrees and arbitrary remaining equations are retained. In particular,
zero is permitted as a remaining equation; no remaining-list regularity or
flatness of the quotient map is required.
-/

@[expose] public noncomputable section

open CategoryTheory Motivic

universe u

namespace MotivicTest.KoszulRegularBlockElimination

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : Function.Surjective f) (t s : List R)
  (hker : RingHom.ker f = Ideal.ofList t)
  (ht : RingTheory.Sequence.IsWeaklyRegular R t) (n : ℕ)

example :
    (Koszul.coefficientComplex (ModuleCat.of R R) (t ++ s)).homology n ≅
      (ModuleCat.restrictScalars f).obj
        ((Koszul.coefficientComplex (ModuleCat.of S S) (s.map f)).homology n) :=
  Koszul.regularBlockHomologyIso f hf t s hker ht n

example :
    Module.length R ((Koszul.coefficientComplex (ModuleCat.of R R) (t ++ [0])).homology n) =
      Module.length S ((Koszul.coefficientComplex (ModuleCat.of S S) [0]).homology n) := by
  have hmap : ([0] : List R).map f = ([0] : List S) := by simp
  exact (Koszul.regularBlockHomology_length f hf t [0] hker ht n).trans
    (congrArg (fun l : List S =>
      Module.length S ((Koszul.coefficientComplex (ModuleCat.of S S) l).homology n)) hmap)

example :
    Module.length R ((Koszul.coefficientComplex (ModuleCat.of R R) (t ++ s)).homology n) =
      Module.length (R ⧸ Ideal.ofList t)
        ((Koszul.coefficientComplex (ModuleCat.of (R ⧸ Ideal.ofList t) (R ⧸ Ideal.ofList t))
          (s.map (Ideal.Quotient.mk (Ideal.ofList t)))).homology n) :=
  Koszul.regularBlockHomology_length (Ideal.Quotient.mk (Ideal.ofList t))
    Ideal.Quotient.mk_surjective t s Ideal.mk_ker ht n

end MotivicTest.KoszulRegularBlockElimination
