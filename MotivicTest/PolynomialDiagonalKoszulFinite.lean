/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.MvPolynomial.Diagonal.Koszul.Finite

/-!
# Consumers of finite polynomial-diagonal resolutions and Tor

The dimension and base commutative ring are arbitrary. Coefficient modules in
the actual Tor comparison are arbitrary as well; their regularity is not assumed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.ChainComplex.Koszul _root_.MvPolynomial.Diagonal

variable (R : Type u) [CommRing R] (n : ℕ)

example : ProjectiveResolution (ModuleCat.of (Ambient R (Fin n))
    (Ambient R (Fin n) ⧸ ideal R (Fin n))) :=
  finiteDiagonalProjectiveResolution R n

example : QuasiIso (finiteDiagonalProjectiveResolution R n).π := inferInstance

example (M : ModuleCat (Ambient R (Fin n))) (i : ℕ) :
    ((Tor (ModuleCat (Ambient R (Fin n))) i).obj M).obj
      (ModuleCat.of _ (Ambient R (Fin n) ⧸ ideal R (Fin n))) ≅
        (coefficientComplex M (differences R n)).homology i :=
  finiteDiagonalTorIsoHomology R n M i

example (M : ModuleCat (Ambient R (Fin n))) :
    IsZero (((Tor (ModuleCat (Ambient R (Fin n))) (n + 1)).obj M).obj
      (ModuleCat.of _ (Ambient R (Fin n) ⧸ ideal R (Fin n)))) :=
  isZero_finiteDiagonalTor_above R n M (n + 1) (by omega)

example (M : ModuleCat R) (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) (i : ℕ) :
    ((Tor (ModuleCat R) i).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s)) ≅
      (coefficientComplex M s).homology i :=
  finiteTorIsoHomology M s hs i

example (M : ModuleCat R) (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (hM : RingTheory.Sequence.IsWeaklyRegular M s) (i : ℕ) :
    IsZero (((Tor (ModuleCat R) (i + 1)).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) :=
  isZero_finiteTor_succ_of_weaklyRegular M s hs hM i
