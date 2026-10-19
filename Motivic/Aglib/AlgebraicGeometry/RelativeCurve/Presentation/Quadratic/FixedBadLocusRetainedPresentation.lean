/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousRetainedPresentation
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.FiniteLocusBadIdeal

/-! # The original étale bad locus is included before the single simultaneous presentation -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry _root_.MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- The actual original étale map supplies its own fixed bad ideal. One subsequent
quadratic tuple controls that entire bad scheme and the prescribed nonreduced closed
scheme, with no assumed good compactification or separately chosen source projection. -/
theorem exists_fixed_bad_locus_retained_presentation
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    [Etale p] [QuasiCompact p] [IsSeparated p]
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ I : Ideal B, I ≠ ⊥ ∧ I ≤ J ∧
    ∃ U : (Spec (.of B)).Opens,
      (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ ∧
      IsFinite (p ∣_ U) ∧
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
    ∃ (N : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2)))
      (V : N.Opens) (t : MvPolynomial (Fin d) k),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) ∧
      (∀ x : Spec (.of B),
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) x =
          Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) P → i x ∈ V) ∧
      (V : Set N) ⊆ Set.range i ∧ IsAffine V.toScheme ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ π ≫ ProjectiveSpace.toSpec _ _) ∧
      Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) P ∈
        PrimeSpectrum.basicOpen t ∧
      IsFinite ((retainedBoundaryInclusion V ≫ π ≫ ProjectiveSpace.toSpec _ _) ∣_
        PrimeSpectrum.basicOpen t) ∧
      IsAffine (((V.ι ≫ π ≫ ProjectiveSpace.toSpec _ _) ⁻¹ᵁ
        PrimeSpectrum.basicOpen t).toScheme) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      ∀ z : Spec (.of (B ⧸ I)),
        (Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) z ∈
            PrimeSpectrum.basicOpen t →
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) z ∈ V := by
  obtain ⟨I, hI, hIJ, U, hU, hp⟩ :=
    exists_fixed_finite_locus_bad_ideal k B p J hJ
  exact ⟨I, hI, hIJ, U, hU, hp,
    exists_simultaneous_retained_presentation k B P I hI g hg d hd q hq⟩

end QuadraticIncidence.InfinityChart
