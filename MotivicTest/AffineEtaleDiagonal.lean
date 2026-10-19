/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineEtale
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of actual affine diagonal stalk presentations

The arbitrary-dimensional consumer mentions the literal scheme diagonal and
stalk map, with explicit tensor coordinate differences. The remaining consumers
exercise polynomial schemes over the nonreduced base `ZMod 4` in dimensions zero,
one, and two.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open RingTheory.Sequence _root_.AlgebraicGeometry.Scheme.Diagonal.Affine

namespace Motivic.MotivicTest.AffineEtaleDiagonal
open _root_.Algebra.TensorProduct

universe u

section General

variable (R S : Type u) (n : ℕ) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
  [Algebra.Etale (MvPolynomial (Fin n) R) S]

example (p : PrimeSpectrum S) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let rs := (List.finRange n).map (fun i =>
      (stalkEquiv R S p).symm
        (algebraMap (S ⊗[R] S)
          (Localization.AtPrime (RelativePolynomial.diagonalPrime R S p.asIdeal))
          (1 ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i) -
            algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X i) ⊗ₜ[R] 1)))
    IsRegular ((pullback f f).presheaf.stalk (pullback.diagonal f p)) rs ∧
      RingHom.ker ((pullback.diagonal f).stalkMap p).hom = Ideal.ofList rs :=
  etale_stalkPresentation R (Fin n) S p (List.finRange n)
    (List.nodup_finRange n) List.mem_finRange

example (p : PrimeSpectrum S) (x : (product R S).presheaf.stalk (diagonal R S p)) :
    Localization.localRingHom
      (p.asIdeal.comap (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)
      p.asIdeal (Algebra.TensorProduct.lmul' R).toRingHom rfl (stalkEquiv R S p x) =
    sourceStalkEquiv R S p
      ((pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S)))).stalkMap p x) :=
  localMultiplication_stalkEquiv R S p x

end General

example (p : PrimeSpectrum (MvPolynomial (Fin 0) (ZMod 4))) :
    IsRegular ((product (ZMod 4) (MvPolynomial (Fin 0) (ZMod 4))).presheaf.stalk
      (diagonal (ZMod 4) (MvPolynomial (Fin 0) (ZMod 4)) p))
      ((List.finRange 0).map (stalkDifference (ZMod 4) (Fin 0)
        (MvPolynomial (Fin 0) (ZMod 4)) p)) ∧
    RingHom.ker ((diagonal (ZMod 4) (MvPolynomial (Fin 0) (ZMod 4))).stalkMap p).hom =
      Ideal.ofList ((List.finRange 0).map (stalkDifference (ZMod 4) (Fin 0)
        (MvPolynomial (Fin 0) (ZMod 4)) p)) :=
  etale_stalkPresentation _ _ _ p _ (List.nodup_finRange 0) List.mem_finRange

example (p : PrimeSpectrum (MvPolynomial (Fin 1) (ZMod 4))) :
    IsRegular ((product (ZMod 4) (MvPolynomial (Fin 1) (ZMod 4))).presheaf.stalk
      (diagonal (ZMod 4) (MvPolynomial (Fin 1) (ZMod 4)) p))
      ((List.finRange 1).map (stalkDifference (ZMod 4) (Fin 1)
        (MvPolynomial (Fin 1) (ZMod 4)) p)) ∧
    RingHom.ker ((diagonal (ZMod 4) (MvPolynomial (Fin 1) (ZMod 4))).stalkMap p).hom =
      Ideal.ofList ((List.finRange 1).map (stalkDifference (ZMod 4) (Fin 1)
        (MvPolynomial (Fin 1) (ZMod 4)) p)) :=
  etale_stalkPresentation _ _ _ p _ (List.nodup_finRange 1) List.mem_finRange

example (p : PrimeSpectrum (MvPolynomial (Fin 2) (ZMod 4))) :
    IsRegular ((product (ZMod 4) (MvPolynomial (Fin 2) (ZMod 4))).presheaf.stalk
      (diagonal (ZMod 4) (MvPolynomial (Fin 2) (ZMod 4)) p))
      ((List.finRange 2).map (stalkDifference (ZMod 4) (Fin 2)
        (MvPolynomial (Fin 2) (ZMod 4)) p)) ∧
    RingHom.ker ((diagonal (ZMod 4) (MvPolynomial (Fin 2) (ZMod 4))).stalkMap p).hom =
      Ideal.ofList ((List.finRange 2).map (stalkDifference (ZMod 4) (Fin 2)
        (MvPolynomial (Fin 2) (ZMod 4)) p)) :=
  etale_stalkPresentation _ _ _ p _ (List.nodup_finRange 2) List.mem_finRange

end Motivic.MotivicTest.AffineEtaleDiagonal
