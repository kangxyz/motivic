/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.PolynomialDiagonalKoszulPair
public import Motivic.RingTheory.MvPolynomial.DiagonalFlat

/-!
# Polynomial diagonal consumers

These checks use arbitrary commutative bases, arbitrary finite coordinate lists,
and arbitrary modules for the actual Tor comparison. No ambient smoothness or
regularity of a coefficient support is an input.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory RingTheory.Sequence MvPolynomial
open Motivic.PolynomialDiagonal Motivic.LocalLength.KoszulPair

variable (R : Type u) [CommRing R]

example {σ : Type*} (l : List σ) (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (l.map (X : σ → MvPolynomial σ R)) :=
  Motivic.MvPolynomial.isWeaklyRegular_X l hl

example {σ : Type*} (l : List σ) (hl : l.Nodup) :
    IsWeaklyRegular (Ambient R σ) (l.map (difference R σ)) :=
  isWeaklyRegular_differences R σ l hl

example [Nontrivial R] {σ : Type*} (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (Ambient R σ) (l.map (difference R σ)) :=
  isRegular_differences R σ l hl

example (n : ℕ) : IsWeaklyRegular (Ambient R (Fin n))
    ((List.finRange n).map (difference R (Fin n))) :=
  isWeaklyRegular_differences R (Fin n) (List.finRange n) (List.nodup_finRange n)

example {σ : Type*} (S : Type*) [CommRing S] [Algebra (Ambient R σ) S]
    [Module.Flat (Ambient R σ) S] (l : List σ) (hl : l.Nodup) :
    IsWeaklyRegular S (l.map (fun i => algebraMap (Ambient R σ) S (difference R σ i))) :=
  isWeaklyRegular_differences_baseChange R σ S l hl

example : IsWeaklyRegular (Ambient R (Fin 3))
    [difference R (Fin 3) 0, difference R (Fin 3) 1, difference R (Fin 3) 2] :=
  isWeaklyRegular_differences R (Fin 3) [0, 1, 2] (by decide)

example {σ : Type*} : RingHom.ker (evaluation R σ) = ideal R σ := ker_evaluation R σ

example {σ : Type*} : (Ambient R σ ⧸ ideal R σ) ≃ₐ[R] MvPolynomial σ R :=
  quotientEquiv R σ

example : ProjectiveResolution (ModuleCat.of (Ambient R (Fin 2))
    (Ambient R (Fin 2) ⧸ ideal R (Fin 2))) := planeProjectiveResolution R

example : QuasiIso (planeProjectiveResolution R).π := inferInstance

example (M : Type u) [AddCommGroup M] [Module (Ambient R (Fin 2)) M] (n : ℕ) :
    ((Tor (ModuleCat (Ambient R (Fin 2))) n).obj (ModuleCat.of _ M)).obj
      (ModuleCat.of _ (Ambient R (Fin 2) ⧸ ideal R (Fin 2))) ≅
        (chainComplex M (difference R (Fin 2) 0) (difference R (Fin 2) 1)).homology n :=
  planeTorIsoHomology R M n
