/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionHom

/-!
# Affine finite-free restriction of scalars for presented algebras

The algebra is the concrete coefficient quotient. Both directions of the
representing equivalence retain the original presentation and tensor product.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open Module MvPolynomial

namespace Algebra.WeilRestriction

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C]
variable {ι κ σ : Type*} [Fintype κ]
variable (b : Basis κ A B) (P : Presentation B C ι σ)
variable {T : Type*} [CommRing T] [Algebra A T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The polynomial map induced by a homomorphism from the coefficient quotient. -/
def quotientPolynomialHom (h : CoordinateQuotient b P.relation →ₐ[A] T) :
    MvPolynomial ι B →ₐ[B] T ⊗[A] B :=
  polynomialHom b (h.comp (Ideal.Quotient.mkₐ A (relationIdeal b P.relation)))

/-- Original presentation relations vanish under the induced polynomial map. -/
theorem quotientPolynomialHom_relation
    (h : CoordinateQuotient b P.relation →ₐ[A] T) (s : σ) :
    quotientPolynomialHom b P h (P.relation s) = 0 := by
  apply (relationIdeal_le_ker_iff b P.relation _).mp _ s
  intro p hp
  change h (Ideal.Quotient.mk _ p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- The actual presentation kernel is killed by the induced polynomial map. -/
theorem quotientPolynomialHom_ker
    (h : CoordinateQuotient b P.relation →ₐ[A] T) :
    RingHom.ker (aeval P.val).toRingHom ≤
      RingHom.ker (quotientPolynomialHom b P h).toRingHom := by
  have hk : RingHom.ker (aeval P.val).toRingHom = P.toGenerators.ker :=
    P.toGenerators.ker_eq_ker_aeval_val.symm
  rw [hk, ← P.span_range_relation_eq_ker]
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact quotientPolynomialHom_relation b P h s

/-- The literal algebra evaluation associated to a quotient-coordinate map. -/
def presentedHom (h : CoordinateQuotient b P.relation →ₐ[A] T) :
    C →ₐ[B] T ⊗[A] B :=
  AlgHom.liftOfSurjective (aeval P.val) P.toGenerators.aeval_val_surjective
    (quotientPolynomialHom b P h) (quotientPolynomialHom_ker b P h)

/-- The induced map has the specified values on the original generators. -/
theorem presentedHom_val (h : CoordinateQuotient b P.relation →ₐ[A] T) (i : ι) :
    presentedHom b P h (P.val i) =
      tensorTuple b (h.comp (Ideal.Quotient.mkₐ A (relationIdeal b P.relation))) i := by
  have := AlgHom.liftOfSurjective_apply (aeval P.val) P.toGenerators.aeval_val_surjective
    (quotientPolynomialHom b P h) (quotientPolynomialHom_ker b P h) (X i)
  simpa only [presentedHom, aeval_X, quotientPolynomialHom, polynomialHom] using this

/-- Coordinate reconstruction turns an original algebra map into a quotient map. -/
def coordinateQuotientHom (g : C →ₐ[B] T ⊗[A] B) :
    CoordinateQuotient b P.relation →ₐ[A] T :=
  Ideal.Quotient.liftₐ _ (coordinateHom b (fun i => g (P.val i))) (by
    apply (relationIdeal_le_ker_iff b P.relation _).mpr
    intro s
    change aeval (tensorTuple b (coordinateHom b (fun i => g (P.val i))))
      (P.relation s) = 0
    have htuple : tensorTuple b (coordinateHom b (fun i => g (P.val i))) =
        fun i => g (P.val i) := funext (coordinateHom_universalGenerator b _)
    rw [htuple, ← comp_aeval, AlgHom.comp_apply, P.aeval_val_relation, map_zero])

/-- Taking scalar coordinates commutes with the quotient map. -/
theorem coordinateQuotientHom_comp_mk (g : C →ₐ[B] T ⊗[A] B) :
    (coordinateQuotientHom b P g).comp (Ideal.Quotient.mkₐ A (relationIdeal b P.relation)) =
      coordinateHom b (fun i => g (P.val i)) :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The actual finite-free representing equivalence for a presented algebra. -/
def homEquiv : (CoordinateQuotient b P.relation →ₐ[A] T) ≃ (C →ₐ[B] T ⊗[A] B) where
  toFun := presentedHom b P
  invFun := coordinateQuotientHom b P
  left_inv h := by
    apply Ideal.Quotient.algHom_ext
    rw [coordinateQuotientHom_comp_mk]
    have hv : (fun i => presentedHom b P h (P.val i)) =
        tensorTuple b (h.comp (Ideal.Quotient.mkₐ A (relationIdeal b P.relation))) :=
      funext (presentedHom_val b P h)
    rw [hv, coordinateHom_tensorTuple]
  right_inv g := by
    apply AlgHom.ext
    intro c
    obtain ⟨p, rfl⟩ := P.toGenerators.aeval_val_surjective c
    have hv : (presentedHom b P (coordinateQuotientHom b P g)).comp (aeval P.val) =
        g.comp (aeval P.val) := by
      ext i
      simp only [AlgHom.comp_apply, aeval_X, presentedHom_val,
        coordinateQuotientHom_comp_mk]
      exact coordinateHom_universalGenerator b (fun i => g (P.val i)) i
    exact DFunLike.congr_fun hv p

/-- The representing equivalence is natural in the test algebra, on original elements. -/
theorem homEquiv_natural {T' : Type*} [CommRing T'] [Algebra A T']
    (h : CoordinateQuotient b P.relation →ₐ[A] T) (g : T →ₐ[A] T') (c : C) :
    homEquiv b P (g.comp h) c =
      Algebra.TensorProduct.map g (AlgHom.id A B) (homEquiv b P h c) := by
  obtain ⟨p, rfl⟩ := P.toGenerators.aeval_val_surjective c
  change presentedHom b P (g.comp h) (aeval P.val p) =
    Algebra.TensorProduct.map g (AlgHom.id A B) (presentedHom b P h (aeval P.val p))
  simp only [presentedHom, AlgHom.liftOfSurjective_apply, quotientPolynomialHom,
    polynomialHom_apply]
  have hm : Algebra.TensorProduct.map
      ((g.comp h).comp (Ideal.Quotient.mkₐ A (relationIdeal b P.relation))) (AlgHom.id A B) =
      (Algebra.TensorProduct.map g (AlgHom.id A B)).comp
        (Algebra.TensorProduct.map
          (h.comp (Ideal.Quotient.mkₐ A (relationIdeal b P.relation))) (AlgHom.id A B)) := by
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t z => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact DFunLike.congr_fun hm (substitution b p)

/-- Evaluation on the representing algebra itself, not an abstract existence witness. -/
def evaluation : C →ₐ[B] CoordinateQuotient b P.relation ⊗[A] B :=
  homEquiv b P (AlgHom.id A _)

/-- Base change of literal evaluation recovers the represented original map. -/
theorem evaluation_map (h : CoordinateQuotient b P.relation →ₐ[A] T) (c : C) :
    Algebra.TensorProduct.map h (AlgHom.id A B) (evaluation b P c) =
      homEquiv b P h c := by
  simpa only [AlgHom.comp_id, evaluation] using
    (homEquiv_natural b P (AlgHom.id A _) h c).symm

/-- Any whole test algebra, including nonreduced ones, lifts uniquely by evaluation. -/
theorem existsUnique_evaluation_lift (g : C →ₐ[B] T ⊗[A] B) :
    ∃! h : CoordinateQuotient b P.relation →ₐ[A] T,
      ∀ c, Algebra.TensorProduct.map h (AlgHom.id A B) (evaluation b P c) = g c := by
  refine ⟨(homEquiv b P).symm g, ?_, ?_⟩
  · intro c
    rw [evaluation_map, Equiv.apply_symm_apply]
  · intro h hh
    apply (homEquiv b P).injective
    rw [Equiv.apply_symm_apply]
    apply AlgHom.ext
    intro c
    rw [← evaluation_map]
    exact hh c

end Algebra.WeilRestriction
