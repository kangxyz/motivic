/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.PrescribedResidueCoordinate
public import Motivic.Aglib.RingTheory.Etale.AdaptedPolynomialCylinder

/-! # A retained polynomial coordinate is the literal affine-line parameter -/
@[expose] public noncomputable section
open MvPolynomial
universe u
namespace Algebra

/-- Splitting off the prescribed coordinate retains its value exactly and
preserves etaleness, giving an affine-line chart over the remaining coordinates. -/
theorem exists_etale_line_map_of_polynomial_map
    (k : Type u) (A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (d : ℕ) (i : Fin d) (h : MvPolynomial (Fin d) k →ₐ[k] A) (hh : h.toRingHom.Etale) :
    ∃ e : Polynomial (MvPolynomial {j : Fin d // j ≠ i} k) →ₐ[k] A,
      e.toRingHom.Etale ∧ e Polynomial.X = h (MvPolynomial.X i) := by
  classical
  let t := (optionEquivLeft k {j : Fin d // j ≠ i}).symm.trans
    (renameEquiv k (Equiv.optionSubtypeNe i))
  refine ⟨h.comp t.toAlgHom, ?_, ?_⟩
  · change (h.toRingHom.comp t.toRingHom).Etale
    exact RingHom.Etale.stableUnderComposition t.toRingHom h.toRingHom
      (RingHom.Etale.of_bijective t.bijective) hh
  · change h (t Polynomial.X) = h (MvPolynomial.X i)
    congr 1
    simp only [t, AlgEquiv.trans_apply, optionEquivLeft_symm_X, renameEquiv_apply,
      rename_X, Equiv.optionSubtypeNe_none]

end Algebra
