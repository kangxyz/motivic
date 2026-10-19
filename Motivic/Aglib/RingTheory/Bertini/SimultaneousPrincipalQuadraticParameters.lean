/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.SimultaneousQuadraticParameters
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Smooth.Bertini.WholeFiberPrincipalNeighborhood

/-! # One actual affine whole-fiber smooth neighborhood for the simultaneous parameters -/
@[expose] public noncomputable section
open _root_.MvPolynomial AlgebraicGeometry CategoryTheory
universe u
namespace QuadraticIncidence

/-- The same quadratic tuple retains every infinity and étale condition while
one genuine principal affine source contains its entire selected fiber and is smooth. -/
theorem exists_simultaneous_principal_quadratic_parameters (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      InfinityChart.NoCommonClosedInfinityZero k R I g d c ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      (∃ r ∉ P.asIdeal, ((algebraMap R (Localization.Away r)).comp
        (aeval (R := k) (fun i => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∃ r : R,
        r - 1 ∈ Ideal.map (aeval (R := k) f).toRingHom
          (Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal) ∧
        (∀ Q : PrimeSpectrum R,
          Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
            Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (aeval (R := k) f).toRingHom)) := by
  obtain ⟨a, c, hc, hZ, hW, he, hs⟩ := exists_simultaneous_quadratic_parameters
    k R P I hI g hg d hd q hq
  obtain ⟨r, hr, hf, hsm⟩ := exists_closedFiber_principal_smooth k
    (MvPolynomial (Fin d) k) R
    (aeval (R := k) (fun i => aeval g (parameterTuple k σ d c i).val)) P 1 hs
  exact ⟨a, c, hc, hZ, hW, he, r, hr, hf,
    IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of R) r).hom, hsm⟩

end QuadraticIncidence
