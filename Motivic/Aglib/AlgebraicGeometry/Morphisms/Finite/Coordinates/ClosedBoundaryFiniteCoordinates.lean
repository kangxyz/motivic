/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite boundary coordinates lifted to the original affine scheme

Noether-normalization coordinates on the actual closed quotient are lifted to
functions on the original ambient ring.  This constructs a finite boundary
projection, not a smooth relative-curve projection: no transversality claim is made.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Actual ambient functions whose restriction to a nonempty closed subscheme
is a finite injective Noether normalization. -/
theorem exists_closedBoundary_finite_coordinates
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] R),
      Function.Injective ((Ideal.Quotient.mkₐ k I).comp f) ∧
      ((Ideal.Quotient.mkₐ k I).comp f).Finite := by
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k (R ⧸ I)
  choose a ha using fun j : Fin n =>
    (Ideal.Quotient.mkₐ_surjective k I) (g (MvPolynomial.X j))
  let f : MvPolynomial (Fin n) k →ₐ[k] R := MvPolynomial.aeval a
  have he : (Ideal.Quotient.mkₐ k I).comp f = g := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [AlgHom.comp_apply, f, MvPolynomial.aeval_X] using ha j
  exact ⟨n, f, he ▸ hg, he ▸ hfin⟩

/-- The original closed immersion followed by the constructed ambient projection
is finite.  The map is literally the restriction of the chosen ambient functions. -/
theorem exists_closedBoundary_finite_projection
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] R),
      Function.Injective ((Ideal.Quotient.mkₐ k I).comp f) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  obtain ⟨n, f, hinj, hfin⟩ := exists_closedBoundary_finite_coordinates k R I hI
  refine ⟨n, f, hinj, ?_⟩
  rw [← Spec.map_comp, IsFinite.SpecMap_iff]
  exact hfin

end AlgebraicGeometry.Scheme
