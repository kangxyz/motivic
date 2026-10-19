/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.TensorProduct.EtaleDiagonal
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of regular local étale diagonal presentations

The generic consumer states the literal coordinate differences and the actual
local multiplication map. Polynomial charts over the nonreduced ring `ZMod 4`
exercise zero, one, and two coordinates without requiring a regular base.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open RingTheory.Sequence _root_.Algebra.TensorProduct.RelativePolynomial

namespace Motivic.MotivicTest.EtaleDiagonal

section General

variable (R S : Type*) (n : ℕ) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
  [Algebra.Etale (MvPolynomial (Fin n) R) S]

example (p : Ideal S) [p.IsPrime] :
    IsRegular (Localization.AtPrime (diagonalPrime R S p))
      ((List.finRange n).map (fun i =>
        algebraMap (S ⊗[R] S) (Localization.AtPrime (diagonalPrime R S p))
          (1 ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i) -
            algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i) ⊗ₜ[R] 1))) ∧
    RingHom.ker (Localization.localRingHom
      (p.comap (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)
      p (Algebra.TensorProduct.lmul' R).toRingHom rfl) =
      Ideal.ofList ((List.finRange n).map (fun i =>
        algebraMap (S ⊗[R] S) (Localization.AtPrime (diagonalPrime R S p))
          (1 ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i) -
            algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i) ⊗ₜ[R] 1))) :=
  etale_localDiagonalPresentation R (Fin n) S p (List.finRange n)
    (List.nodup_finRange n) List.mem_finRange

end General

example (p : Ideal (MvPolynomial (Fin 0) (ZMod 4))) [p.IsPrime] :
    IsRegular (Localization.AtPrime
      (diagonalPrime (ZMod 4) (MvPolynomial (Fin 0) (ZMod 4)) p))
      ((List.finRange 0).map
        (localDifference (ZMod 4) (Fin 0) (MvPolynomial (Fin 0) (ZMod 4)) p)) ∧
    RingHom.ker (localMultiplication (ZMod 4) (MvPolynomial (Fin 0) (ZMod 4)) p) =
      Ideal.ofList ((List.finRange 0).map
        (localDifference (ZMod 4) (Fin 0) (MvPolynomial (Fin 0) (ZMod 4)) p)) :=
  etale_localDiagonalPresentation _ _ _ p _ (List.nodup_finRange 0) List.mem_finRange

example (p : Ideal (MvPolynomial (Fin 1) (ZMod 4))) [p.IsPrime] :
    IsRegular (Localization.AtPrime
      (diagonalPrime (ZMod 4) (MvPolynomial (Fin 1) (ZMod 4)) p))
      ((List.finRange 1).map
        (localDifference (ZMod 4) (Fin 1) (MvPolynomial (Fin 1) (ZMod 4)) p)) ∧
    RingHom.ker (localMultiplication (ZMod 4) (MvPolynomial (Fin 1) (ZMod 4)) p) =
      Ideal.ofList ((List.finRange 1).map
        (localDifference (ZMod 4) (Fin 1) (MvPolynomial (Fin 1) (ZMod 4)) p)) :=
  etale_localDiagonalPresentation _ _ _ p _ (List.nodup_finRange 1) List.mem_finRange

example (p : Ideal (MvPolynomial (Fin 2) (ZMod 4))) [p.IsPrime] :
    IsRegular (Localization.AtPrime
      (diagonalPrime (ZMod 4) (MvPolynomial (Fin 2) (ZMod 4)) p))
      ((List.finRange 2).map
        (localDifference (ZMod 4) (Fin 2) (MvPolynomial (Fin 2) (ZMod 4)) p)) ∧
    RingHom.ker (localMultiplication (ZMod 4) (MvPolynomial (Fin 2) (ZMod 4)) p) =
      Ideal.ofList ((List.finRange 2).map
        (localDifference (ZMod 4) (Fin 2) (MvPolynomial (Fin 2) (ZMod 4)) p)) :=
  etale_localDiagonalPresentation _ _ _ p _ (List.nodup_finRange 2) List.mem_finRange

end Motivic.MotivicTest.EtaleDiagonal
