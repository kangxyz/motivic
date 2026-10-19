/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.NormalCompactification
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ClosedProjectionFinite
public import Motivic.Aglib.RingTheory.Bertini.SimultaneousPrincipalQuadraticParameters

/-! # One generated tuple supplies the compactification, whole boundary and whole smooth fiber -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart

/-- Actual target-presentation geometry over an infinite field: a single original tuple
produces a normal finite compactification, its complete finite infinity, finiteness of
the original nonreduced prescribed closed scheme, and an affine whole-fiber smooth open. -/
theorem exists_simultaneous_quadratic_compactification
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    (I : Ideal B) (hI : I ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      (∃ r : B,
        r - 1 ∈ Ideal.map (quadraticCoordinateHom k B g d c)
          (Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal) ∧
        (∀ Q : PrimeSpectrum B,
          Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal =
            Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)))) ∧
    ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2))) (b : D ⟶ N),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsClosedImmersion b ∧
      IsFinite (b ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨a, c, hc, hZ, hW, he, hs⟩ := exists_simultaneous_principal_quadratic_parameters
    k B P I hI g hg d hd q hq
  obtain ⟨r, hr, he⟩ := he
  exact ⟨a, c, hc, quadraticClosedTuple_isFinite k B g d I hg c hZ, hs,
    exists_quadratic_normal_compactification k B g hg d a c hW P r hr he⟩

end QuadraticIncidence.InfinityChart
