/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.TensorProduct.PolynomialRelations
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of the polynomial relative-tensor quotient

The examples retain an explicit polynomial map and both tensor factors. Zero,
one, and two variables are also checked over the nonreduced ring `ZMod 4`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open _root_.Algebra.TensorProduct.RelativePolynomial

namespace Motivic.MotivicTest.RelativePolynomialTensor

variable {R σ S : Type*} [CommRing R] [CommRing S] [Algebra R S]

example (g : MvPolynomial σ R →ₐ[R] S) :
    letI := g.toAlgebra
    (S ⊗[R] S ⧸ Ideal.span (Set.range (fun i : σ =>
      1 ⊗ₜ[R] g (MvPolynomial.X i) - g (MvPolynomial.X i) ⊗ₜ[R] 1))) ≃ₐ[R]
      S ⊗[MvPolynomial σ R] S := quotientEquivOfHom g

example (g : MvPolynomial σ R →ₐ[R] S) (a b : S) :
    letI := g.toAlgebra
    quotientEquivOfHom g (Ideal.Quotient.mk _ (a ⊗ₜ[R] b)) =
      a ⊗ₜ[MvPolynomial σ R] b := quotientEquivOfHom_mk_tmul g a b

example (g : MvPolynomial σ R →ₐ[R] S) (a b : S) :
    letI := g.toAlgebra
    (quotientEquivOfHom g).symm (a ⊗ₜ[MvPolynomial σ R] b) =
      Ideal.Quotient.mk _ (a ⊗ₜ[R] b) := quotientEquivOfHom_symm_tmul g a b

example : RingHom.ker (toRelative (ZMod 4) (Fin 0) (MvPolynomial (Fin 0) (ZMod 4))) =
    ideal (ZMod 4) (Fin 0) (MvPolynomial (Fin 0) (ZMod 4)) := ker_toRelative _ _ _

example : RingHom.ker (toRelative (ZMod 4) (Fin 1) (MvPolynomial (Fin 1) (ZMod 4))) =
    ideal (ZMod 4) (Fin 1) (MvPolynomial (Fin 1) (ZMod 4)) := ker_toRelative _ _ _

example : RingHom.ker (toRelative (ZMod 4) (Fin 2) (MvPolynomial (Fin 2) (ZMod 4))) =
    ideal (ZMod 4) (Fin 2) (MvPolynomial (Fin 2) (ZMod 4)) := ker_toRelative _ _ _

example [Algebra (ZMod 4) S] (g : MvPolynomial (Fin 2) (ZMod 4) →ₐ[ZMod 4] S)
    (a b : S) :
    letI := g.toAlgebra
    quotientEquivOfHom g (Ideal.Quotient.mk _ (a ⊗ₜ[ZMod 4] b)) =
      a ⊗ₜ[MvPolynomial (Fin 2) (ZMod 4)] b := quotientEquivOfHom_mk_tmul g a b

end Motivic.MotivicTest.RelativePolynomialTensor
