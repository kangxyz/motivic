/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.AdaptedPolynomialChart
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Option

/-! # Splitting off the unchanged Cartier equation as the affine-line coordinate -/

@[expose] public noncomputable section

universe u

namespace MvPolynomial

/-- Split off a specified variable, leaving all other variables in the coefficient ring. -/
def splitVariableEquiv (k : Type u) [CommRing k] {ι : Type u} (i : ι) :
    MvPolynomial ι k ≃ₐ[k] Polynomial (MvPolynomial {j : ι // j ≠ i} k) := by
  classical
  exact (renameEquiv k (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft k _)

@[simp]
theorem splitVariableEquiv_symm_X (k : Type u) [CommRing k] {ι : Type u} (i : ι) :
    (splitVariableEquiv k i).symm Polynomial.X = X i := by
  classical
  simp [splitVariableEquiv, renameEquiv_apply]

end MvPolynomial

namespace Algebra

/-- An actual polynomial-cylinder chart whose last coordinate is the original
regular divisor equation. This is an existence theorem, not chart data assumed
in place of smoothness. -/
theorem exists_etale_polynomial_cylinder_preserving_regular_generator
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Smooth k R]
    (t : R) (ht : IsRegular t) [FormallySmooth k (R ⧸ Ideal.span {t})]
    (p : Ideal R) [p.IsPrime] (htp : t ∈ p) :
    ∃ (ι : Type u), Finite ι ∧ ∃ r ∉ p,
      ∃ ψ : Polynomial (MvPolynomial ι k) →+* Localization.Away r,
        ψ.Etale ∧ ψ Polynomial.X = algebraMap R (Localization.Away r) t := by
  classical
  obtain ⟨s, hts, hs, r, hr, hφ⟩ :=
    exists_etale_polynomial_chart_preserving_regular_generator k R t ht p htp
  let i : s := ⟨t, hts⟩
  let e := MvPolynomial.splitVariableEquiv k i
  let φ := (algebraMap R (Localization.Away r)).comp
    (MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R))).toRingHom
  let ψ := φ.comp e.symm.toRingHom
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
