/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteResolution

/-!
# Consumers of the genuine finite regular-sequence resolution

These examples apply the constructed quotient-coefficient comparison, positive
exactness induction, and actual projective resolution of the generated ideal
quotient. Regularity is the mathematical hypothesis; no resolution is supplied.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory
open Motivic.Koszul

variable {R : Type u} [CommRing R] (M : ModuleCat R) (s : List R) (a : R)

example (ha : IsSMulRegular M a) (n : ℕ) :
    IsSMulRegular ((coefficientComplex M s).X n) a :=
  coefficientComplex_isSMulRegular M s a ha n

example : quotientComplex a (coefficientComplex M s) ≅
    coefficientComplex ((scalarQuotientFunctor a).obj M) s :=
  coefficientQuotientIso a M s

example (hs : RingTheory.Sequence.IsWeaklyRegular M s) (n : ℕ) :
    (coefficientComplex M s).ExactAt (n + 1) :=
  coefficient_exactAt_succ_of_weaklyRegular M s hs n

example (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList s)) :=
  finiteProjectiveResolution s hs

example (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    (finiteProjectiveResolution s hs).complex = chainComplex s := rfl

example (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    (finiteProjectiveResolution s hs).π = idealAugmentation s := rfl

example (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    QuasiIso (finiteProjectiveResolution s hs).π := inferInstance

example (hs : RingTheory.Sequence.IsRegular R s) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList s)) :=
  regularProjectiveResolution s hs
