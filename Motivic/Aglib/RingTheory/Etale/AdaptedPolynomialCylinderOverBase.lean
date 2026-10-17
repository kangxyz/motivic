/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.AdaptedPolynomialCylinder

/-! # Adapted polynomial-cylinder charts over the original base field -/

@[expose] public noncomputable section

universe u

namespace Algebra

/-- The adapted cylinder chart is an algebra homomorphism over the original
field, while its last variable remains the prescribed divisor equation. -/
theorem exists_etale_polynomial_cylinder_algHom_preserving_regular_generator
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Smooth k R]
    (t : R) (ht : IsRegular t) [FormallySmooth k (R ⧸ Ideal.span {t})]
    (p : Ideal R) [p.IsPrime] (htp : t ∈ p) :
    ∃ (ι : Type u), Finite ι ∧ ∃ r ∉ p,
      ∃ ψ : Polynomial (MvPolynomial ι k) →ₐ[k] Localization.Away r,
        ψ.toRingHom.Etale ∧ ψ Polynomial.X = algebraMap R (Localization.Away r) t := by
  classical
  obtain ⟨s, hts, hs, r, hr, hφ⟩ :=
    exists_etale_polynomial_chart_preserving_regular_generator k R t ht p htp
  let i : s := ⟨t, hts⟩
  let e := MvPolynomial.splitVariableEquiv k i
  let φ : MvPolynomial s k →ₐ[k] Localization.Away r :=
    (IsScalarTower.toAlgHom k R (Localization.Away r)).comp
      (MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R)))
  let ψ := φ.comp e.symm.toAlgHom
  let : Fintype s := hs.fintype
  refine ⟨{j : s // j ≠ i}, inferInstance, r, hr, ψ, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective e.symm.bijective) hφ
  · change φ (e.symm Polynomial.X) = _
    rw [MvPolynomial.splitVariableEquiv_symm_X]
    change (algebraMap R (Localization.Away r))
      ((MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R))) (.X i)) = _
    rw [MvPolynomial.aeval_X]

end Algebra
