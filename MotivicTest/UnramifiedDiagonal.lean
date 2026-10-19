/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.TensorProduct.UnramifiedDiagonal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of the actual local diagonal kernel

The tests use the actual local ring homomorphism and the literal generated ideal.
They include etale polynomial coordinates and polynomial rings over `ZMod 4`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open _root_.Algebra.TensorProduct.RelativePolynomial

namespace Motivic.MotivicTest.UnramifiedDiagonal

section General

variable (R σ S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]
  [Algebra.Etale (MvPolynomial σ R) S]

example (p : Ideal S) [p.IsPrime] :
    RingHom.ker (Localization.localRingHom
      (p.comap (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)
      p (Algebra.TensorProduct.lmul' R).toRingHom rfl) =
    (Ideal.span (Set.range (fun i : σ =>
      1 ⊗ₜ[R] algebraMap (MvPolynomial σ R) S (MvPolynomial.X i) -
        algebraMap (MvPolynomial σ R) S (MvPolynomial.X i) ⊗ₜ[R] 1))).map
      (algebraMap (S ⊗[R] S) (Localization.AtPrime (diagonalPrime R S p))) :=
  ker_localMultiplication R σ S p

end General

example (p : Ideal (MvPolynomial (Fin 0) (ZMod 4))) [p.IsPrime] :
    RingHom.ker (localMultiplication (ZMod 4) (MvPolynomial (Fin 0) (ZMod 4)) p) =
      (ideal (ZMod 4) (Fin 0) (MvPolynomial (Fin 0) (ZMod 4))).map
        (algebraMap _ (Localization.AtPrime
          (diagonalPrime (ZMod 4) (MvPolynomial (Fin 0) (ZMod 4)) p))) :=
  ker_localMultiplication _ _ _ p

example (p : Ideal (MvPolynomial (Fin 1) (ZMod 4))) [p.IsPrime] :
    RingHom.ker (localMultiplication (ZMod 4) (MvPolynomial (Fin 1) (ZMod 4)) p) =
      (ideal (ZMod 4) (Fin 1) (MvPolynomial (Fin 1) (ZMod 4))).map
        (algebraMap _ (Localization.AtPrime
          (diagonalPrime (ZMod 4) (MvPolynomial (Fin 1) (ZMod 4)) p))) :=
  ker_localMultiplication _ _ _ p

example (p : Ideal (MvPolynomial (Fin 2) (ZMod 4))) [p.IsPrime] :
    RingHom.ker (localMultiplication (ZMod 4) (MvPolynomial (Fin 2) (ZMod 4)) p) =
      (ideal (ZMod 4) (Fin 2) (MvPolynomial (Fin 2) (ZMod 4))).map
        (algebraMap _ (Localization.AtPrime
          (diagonalPrime (ZMod 4) (MvPolynomial (Fin 2) (ZMod 4)) p))) :=
  ker_localMultiplication _ _ _ p

end Motivic.MotivicTest.UnramifiedDiagonal
