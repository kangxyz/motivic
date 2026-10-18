/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.FiniteExtensionResiduePolynomialAvoidance

/-! # Evaluate the entire specialized residue-polynomial fiber at a field point -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace MvPolynomial

universe u

/-- A unit on the entire specialized coefficient fiber is nonzero under the
literal residue-polynomial evaluation at every compatible field-valued point. -/
theorem eval₂_ne_zero_of_isUnit_residueFiber
    (k κ L K : Type u) [Field k] [Field κ] [Field L] [Field K]
    [Algebra k κ] [Algebra k L] [Algebra k K] [Algebra L K] [Algebra κ K]
    [IsScalarTower k L K] [IsScalarTower k κ K]
    {τ : Type u} (T : MvPolynomial τ κ) (c : τ → L)
    (hu : let : Algebra (MvPolynomial τ k) L :=
        (eval₂Hom (algebraMap k L) c).toAlgebra
      IsUnit (1 ⊗ₜ[MvPolynomial τ k] (residueCoefficientEquiv k κ τ).symm T :
        L ⊗[MvPolynomial τ k] (MvPolynomial τ k ⊗[k] κ))) :
    eval₂ (algebraMap κ K) (algebraMap L K ∘ c) T ≠ 0 := by
  let P := MvPolynomial τ k
  let : Algebra P L := (eval₂Hom (algebraMap k L) c).toAlgebra
  let : IsScalarTower k P L := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap k L r = eval₂ (algebraMap k L) c (C r)
    simp
  let φ : L ⊗[k] κ →ₐ[k] K := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom k L K) (IsScalarTower.toAlgHom k κ K)
    (fun _ _ => Commute.all _ _)
  let ψ : L ⊗[P] (P ⊗[k] κ) →+* K := φ.toRingHom.comp
    (Algebra.TensorProduct.cancelBaseChange k P L L κ).toRingHom
  have hC (a : κ) : (residueCoefficientEquiv k κ τ).symm (C a) =
      (1 : P) ⊗ₜ[k] a := by
    apply (residueCoefficientEquiv k κ τ).injective
    simp [residueCoefficientEquiv, Algebra.smul_def]
  have hX (i : τ) : (residueCoefficientEquiv k κ τ).symm (X i) =
      (X i : P) ⊗ₜ[k] (1 : κ) := by
    apply (residueCoefficientEquiv k κ τ).injective
    simp [residueCoefficientEquiv]
  have he (T : MvPolynomial τ κ) :
      ψ (1 ⊗ₜ[P] (residueCoefficientEquiv k κ τ).symm T) =
        eval₂ (algebraMap κ K) (algebraMap L K ∘ c) T := by
    have hehom : (ψ.comp
        (Algebra.TensorProduct.includeRight : (P ⊗[k] κ) →ₐ[P]
          L ⊗[P] (P ⊗[k] κ)).toRingHom).comp
        (residueCoefficientEquiv k κ τ).symm.toRingHom =
        eval₂Hom (algebraMap κ K) (algebraMap L K ∘ c) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change ψ (1 ⊗ₜ[P] (residueCoefficientEquiv k κ τ).symm (C a)) = _
        rw [hC]
        simp [ψ, φ]
      · intro i
        change ψ (1 ⊗ₜ[P] (residueCoefficientEquiv k κ τ).symm (X i)) = _
        rw [hX]
        suffices (algebraMap P L) (X i) = c i by
          simpa [ψ, φ, Algebra.smul_def] using this
        change eval₂ (algebraMap k L) c (X i) = c i
        exact eval₂_X _ _ _
    exact DFunLike.congr_fun hehom T
  rw [← he]
  exact (hu.map ψ).ne_zero

end MvPolynomial
