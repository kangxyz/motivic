/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.NormalCompactification
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ClosedProjectionFinite
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Smooth.Bertini.WholeFiberPrincipalNeighborhood

/-! # Chosen original quadratic parameters supply actual compactification geometry -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart

/-- Assemble actual geometry from chosen original parameters. No cardinality
assumption or parameter-choice theorem is used. The prescribed quotient stays
nonreduced and its original quotient map is retained. -/
theorem exists_chosen_quadratic_compactification
    (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    (I : Ideal B) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (hZ : NoCommonClosedInfinityZero k B I g d c)
    (hW : NoCommonInfinityZero k B g d (prependParameters k d a c))
    (he : ∃ r ∉ P.asIdeal, ((algebraMap B (Localization.Away r)).comp
      (aeval (R := k) (fun i => aeval g
        (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale)
    (hs : ∀ Q : PrimeSpectrum B,
      Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal =
        Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal →
      ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
        (Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away r)).comp
          (quadraticCoordinateHom k B g d c))))) :
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
  obtain ⟨r₀, hr₀, hf₀, hsm₀⟩ := exists_closedFiber_principal_smooth k
    (MvPolynomial (Fin d) k) B
    (aeval (R := k) (fun i => aeval g (parameterTuple k σ d c i).val)) P 1 hs
  obtain ⟨r, hr, he⟩ := he
  exact ⟨quadraticClosedTuple_isFinite k B g d I hg c hZ,
    ⟨r₀, hr₀, hf₀,
      IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of B) r₀).hom, hsm₀⟩,
    exists_quadratic_normal_compactification k B g hg d a c hW P r hr he⟩

end QuadraticIncidence.InfinityChart
