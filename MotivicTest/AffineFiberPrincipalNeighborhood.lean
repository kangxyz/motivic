/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.AffineFiberPrincipalNeighborhood
public import Lean

/-! # Actual principal affine neighborhoods of whole closed fibers -/
public noncomputable section
open CategoryTheory AlgebraicGeometry QuadraticIncidence MvPolynomial
universe u
namespace MotivicTest.AffineFiberPrincipalNeighborhood

/-- The original ideal can have nilpotents; no radical replacement is required. -/
theorem original_ideal_neighborhood (R : Type u) [CommRing R] (J : Ideal R)
    (U : TopologicalSpace.Opens (PrimeSpectrum R))
    (h : PrimeSpectrum.zeroLocus (J : Set R) ⊆ U) :
    ∃ r : R, r - 1 ∈ J ∧ PrimeSpectrum.basicOpen r ≤ U :=
  PrimeSpectrum.exists_basicOpen_between_zeroLocus R J U h

/-- A direct consumer supplies no smooth-locus or affine-neighborhood premise. -/
theorem original_tuple_actual_affine_neighborhood (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : PrimeSpectrum R) [p.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      let φ := (aeval (R := k) f).toRingHom
      ∃ r : R, r - 1 ∈ Ideal.map φ (Ideal.comap φ p.asIdeal) ∧
        (∀ x : PrimeSpectrum R, Ideal.comap φ p.asIdeal = Ideal.comap φ x.asIdeal →
          x ∈ PrimeSpectrum.basicOpen r) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          ((Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ≫
            Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨c, hc, r, hr, hf, hs⟩ :=
    exists_wholeFiber_principal_smooth_projection k R p g hg d hd q hq
  exact ⟨c, hc, r, hr, hf, IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of R) r).hom, hs⟩

open Lean in
run_cmd do
  for name in #[``original_ideal_neighborhood, ``original_tuple_actual_affine_neighborhood,
      ``PrimeSpectrum.exists_basicOpen_between_zeroLocus, ``sourceLocal_on_iSup,
      ``exists_principal_smooth_neighborhood, ``comap_closedPoint_isMaximal,
      ``exists_wholeFiber_principal_smooth_projection] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original ideal, entire fiber, actual affine principal open and smooth map: audited."

end MotivicTest.AffineFiberPrincipalNeighborhood
