/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Formal étaleness through a represented restriction of scalars

This leaf transports square-zero lifting through an explicit natural equivalence
of algebra-homomorphism sets. It does not assume or assert that an arbitrary
restriction of scalars is representable. The finite-free coordinate construction
must supply the actual equivalence before this criterion can be applied.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.TensorProduct

variable {A B T T' : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']

variable (B) in
/-- Scalar extension on the left tensor factor, regarded over the right factor. -/
def rTensorRight (f : T →ₐ[A] T') : T ⊗[A] B →ₐ[B] T' ⊗[A] B where
  __ := (map f (AlgHom.id A B)).toRingHom
  commutes' b := by
    change map f (AlgHom.id A B) (1 ⊗ₜ[A] b) = 1 ⊗ₜ[A] b
    simp only [map_tmul, map_one, AlgHom.id_apply]

@[simp]
lemma rTensorRight_apply (f : T →ₐ[A] T') (x : T ⊗[A] B) :
    rTensorRight B f x = map f (AlgHom.id A B) x := rfl

/-- The tensor-quotient equivalence retains the algebra structure of the right factor. -/
def quotientTensorRightEquiv (I : Ideal T) :
    (T ⧸ I) ⊗[A] B ≃ₐ[B]
      (T ⊗[A] B) ⧸ I.map (algebraMap T (T ⊗[A] B)) where
  __ := (quotientTensorEquiv (R := A) A B T I).toRingEquiv
  commutes' _ := rfl

@[simp]
lemma quotientTensorRightEquiv_symm_mk_tmul (I : Ideal T) (t : T) (b : B) :
    (quotientTensorRightEquiv (A := A) (B := B) I).symm
      (Ideal.Quotient.mk (I.map (algebraMap T (T ⊗[A] B))) (t ⊗ₜ[A] b)) =
        Ideal.Quotient.mk I t ⊗ₜ[A] b := rfl

/-- Under the tensor-quotient equivalence, the original quotient map is scalar extension. -/
lemma quotientTensorRightEquiv_symm_comp_mk (I : Ideal T) :
    (quotientTensorRightEquiv (A := A) (B := B) I).symm.toAlgHom.comp
        (Ideal.Quotient.mkₐ B (I.map (algebraMap T (T ⊗[A] B)))) =
      rTensorRight B (Ideal.Quotient.mkₐ A I) := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul t b => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Algebra.TensorProduct

namespace Algebra.FormallyEtale

variable {A B C T : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [CommRing C] [Algebra B C] [CommRing T] [Algebra A T]

/-- Formal étaleness gives unique lifting along the scalar extension of a square-zero quotient.
No flatness hypothesis is needed for the tensor-quotient identification. -/
theorem tensor_quotient_comp_bijective [FormallyEtale B C]
    (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Function.Bijective
      ((TensorProduct.rTensorRight B (Ideal.Quotient.mkₐ A I)).comp :
        (C →ₐ[B] T ⊗[A] B) → C →ₐ[B] (T ⧸ I) ⊗[A] B) := by
  let J : Ideal (T ⊗[A] B) := I.map (algebraMap T (T ⊗[A] B))
  have hJ : J ^ 2 = ⊥ := by
    dsimp only [J]
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  let e := TensorProduct.quotientTensorRightEquiv (A := A) (B := B) I
  have hpost : Function.Bijective
      (fun f : C →ₐ[B] (T ⊗[A] B) ⧸ J => e.symm.toAlgHom.comp f) := by
    constructor
    · intro f g h
      apply AlgHom.ext
      intro c
      exact e.symm.injective (AlgHom.congr_fun h c)
    · intro f
      refine ⟨e.toAlgHom.comp f, ?_⟩
      apply AlgHom.ext
      intro c
      exact e.symm_apply_apply (f c)
  have hcomp := hpost.comp (comp_bijective B C J hJ)
  convert hcomp using 1
  funext f
  change (TensorProduct.rTensorRight B (Ideal.Quotient.mkₐ A I)).comp f =
    e.symm.toAlgHom.comp ((Ideal.Quotient.mkₐ B J).comp f)
  rw [← AlgHom.comp_assoc]
  exact congrArg (fun g => g.comp f)
    (TensorProduct.quotientTensorRightEquiv_symm_comp_mk (A := A) (B := B) I).symm

end Algebra.FormallyEtale

namespace Algebra.WeilRestriction

universe uA uB uC uD

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra B C]
  [CommRing D] [Algebra A D]

/-- A natural representing Hom equivalence transports formal étaleness.

The only compatibility required is with the actual quotient maps, evaluated on
all elements of the original algebra `C`. In applications the finite-free
coordinate quotient supplies `e` and its naturality, rather than taking a
representability or étaleness theorem family as an input. -/
theorem formallyEtale_of_homEquiv [FormallyEtale B C]
    (e : ∀ (T : Type max uA uD) [CommRing T] [Algebra A T],
      (D →ₐ[A] T) ≃ (C →ₐ[B] T ⊗[A] B))
    (he : ∀ (T : Type max uA uD) [CommRing T] [Algebra A T]
      (I : Ideal T) (f : D →ₐ[A] T) (c : C),
      e (T ⧸ I) ((Ideal.Quotient.mkₐ A I).comp f) c =
        TensorProduct.map (Ideal.Quotient.mkₐ A I) (AlgHom.id A B) (e T f c)) :
    FormallyEtale A D := by
  apply FormallyEtale.iff_comp_bijective.mpr
  intro T _ _ I hI
  have hnat (f : D →ₐ[A] T) :
      e (T ⧸ I) ((Ideal.Quotient.mkₐ A I).comp f) =
        (TensorProduct.rTensorRight B (Ideal.Quotient.mkₐ A I)).comp (e T f) := by
    apply AlgHom.ext
    intro c
    exact he T I f c
  have hbij := FormallyEtale.tensor_quotient_comp_bijective (A := A) (B := B) (C := C) I hI
  constructor
  · intro f g h
    apply (e T).injective
    apply hbij.injective
    rw [← hnat, ← hnat, h]
  · intro f
    obtain ⟨g, hg⟩ := hbij.surjective (e (T ⧸ I) f)
    refine ⟨(e T).symm g, ?_⟩
    apply (e (T ⧸ I)).injective
    rw [hnat, Equiv.apply_symm_apply]
    exact hg

end Algebra.WeilRestriction
