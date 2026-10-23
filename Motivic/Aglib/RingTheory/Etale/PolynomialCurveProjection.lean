/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # The literal base-coordinate projection of a polynomial curve chart -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open _root_.MvPolynomial
universe u v
namespace RingHom

/-- A polynomial line is standard smooth of relative dimension one. -/
theorem polynomial_C_standardSmooth_one (A : Type u) [CommRing A] :
    (Polynomial.C : A →+* Polynomial A).IsStandardSmoothOfRelativeDimension 1 := by
  let e := MvPolynomial.uniqueAlgEquiv A (Fin 1)
  have h : (algebraMap A (MvPolynomial (Fin 1) A)).IsStandardSmoothOfRelativeDimension 1 :=
    (isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance
  have he := (IsStandardSmoothOfRelativeDimension.equiv e.toRingEquiv).comp h
  have heq : e.toRingEquiv.toRingHom.comp (algebraMap A (MvPolynomial (Fin 1) A)) =
      Polynomial.C := by
    apply RingHom.ext
    intro a
    exact e.commutes a
  change IsStandardSmoothOfRelativeDimension (0 + 1)
    (e.toRingEquiv.toRingHom.comp (algebraMap A (MvPolynomial (Fin 1) A))) at he
  rw [heq] at he
  exact he

/-- Forgetting the first variable is the original smooth relative-line projection. -/
theorem mvPolynomial_rename_succ_standardSmooth_one
    (k : Type u) [CommRing k] (d : ℕ) :
    (MvPolynomial.rename Fin.succ : MvPolynomial (Fin d) k →ₐ[k]
      MvPolynomial (Fin (d + 1)) k).toRingHom.IsStandardSmoothOfRelativeDimension 1 := by
  let e := MvPolynomial.finSuccEquiv k d
  have h := (IsStandardSmoothOfRelativeDimension.equiv e.symm.toRingEquiv).comp
    (polynomial_C_standardSmooth_one (MvPolynomial (Fin d) k))
  have heq : e.symm.toRingHom.comp Polynomial.C =
      (MvPolynomial.rename Fin.succ : MvPolynomial (Fin d) k →ₐ[k]
        MvPolynomial (Fin (d + 1)) k).toRingHom := by
    apply RingHom.ext
    intro f
    apply e.injective
    change e (e.symm (Polynomial.C f)) = e ((MvPolynomial.rename Fin.succ) f)
    rw [e.apply_symm_apply]
    induction f using MvPolynomial.induction_on with
    | C c => simpa only [rename_C] using! (e.commutes c).symm
    | add f g hf hg => simpa only [map_add] using congrArg₂ (· + ·) hf hg
    | mul_X f j hf =>
      rw [map_mul, map_mul, map_mul, rename_X, show e (X j.succ) =
        Polynomial.C (X j) from finSuccEquiv_X_succ]
      exact congrArg (· * Polynomial.C (X j)) hf
  change IsStandardSmoothOfRelativeDimension (0 + 1)
    (e.symm.toRingHom.comp Polynomial.C) at h
  rw [heq] at h
  exact h

/-- An étale chart with literal coordinates `(t,g)` makes the same base `g`
standard smooth of relative dimension one. -/
theorem etale_cons_base_standardSmooth_one
    (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]
    {d : ℕ} (t : A) (g : Fin d → A)
    (h : (MvPolynomial.aeval (R := k) (Fin.cons (α := fun _ => A) t g)).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) g).toRingHom.IsStandardSmoothOfRelativeDimension 1 := by
  let f := (MvPolynomial.aeval (R := k) (Fin.cons (α := fun _ => A) t g)).toRingHom
  have hf : f.IsStandardSmoothOfRelativeDimension 0 := by
    let := f.toAlgebra
    change Algebra.IsStandardSmoothOfRelativeDimension 0 _ _
    exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp h
  have hh := hf.comp (mvPolynomial_rename_succ_standardSmooth_one k d)
  have heq : f.comp (MvPolynomial.rename Fin.succ).toRingHom =
      (MvPolynomial.aeval (R := k) g).toRingHom := by
    ext <;> simp [f]
  simpa only [zero_add, heq] using hh

end RingHom
