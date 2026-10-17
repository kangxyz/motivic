/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.FixedBadLocusRetainedPresentation
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.NormalRetainedBaseRestriction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.QuotientRetainedBadCover
public import Lean

/-! # The original étale problem supplies its finite bad scheme and actual target presentation -/
public noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve QuadraticIncidence QuadraticIncidence.InfinityChart
universe u

/-- No finite map, compactification, rank condition, rationality, or good bad ideal is input. -/
example (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ)) :
    ∃ (I : Ideal B) (U : (Spec (.of B)).Opens)
      (c : Fin d × Exponent σ → k) (N : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2)))
      (V : N.Opens) (t : MvPolynomial (Fin d) k),
      I ≠ ⊥ ∧ I ≤ J ∧ IsFinite (p ∣_ U) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      IsIntegral N ∧ IsFinite π ∧ IsOpenImmersion i ∧ i P ∈ V ∧
      IsAffine V.toScheme ∧ SmoothOfRelativeDimension 1 (V.ι ≫ π ≫ ProjectiveSpace.toSpec _ _) ∧
      Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) P ∈
        PrimeSpectrum.basicOpen t ∧
      IsFinite ((retainedBoundaryInclusion V ≫ π ≫ ProjectiveSpace.toSpec _ _) ∣_
        PrimeSpectrum.basicOpen t) ∧
      (∀ z : Spec (.of (B ⧸ I)),
        Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c))) z ∈
            PrimeSpectrum.basicOpen t →
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) z ∈ V) := by
  obtain ⟨I, hI, hIJ, U, _, hp, _, c, _, N, i, π, V, t,
    hN, _, _, hi, hπ, _, _, hwhole, _, ha, hs, ht, hb, _, hfin, hz⟩ :=
    exists_fixed_bad_locus_retained_presentation k B P p J hJ g hg d hd 1 one_ne_zero
  exact ⟨I, U, c, N, i, π, V, t, hI, hIJ, hp, hfin, hN, hπ, hi,
    hwhole P rfl, ha, hs, ht, hb, hz⟩

example (R : Type u) [CommRing R] {N : Scheme.{u}}
    (π : N ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite π]
    (T : (Spec (.of R)).Opens) [IsAffine T.toScheme] :
    IsFinite (finiteProjectiveBaseRestriction R (ULift.{u} (Fin 2)) π T) := inferInstance

open Lean in
run_cmd do
  for name in #[``exists_fixed_finite_locus_bad_ideal,
      ``exists_simultaneous_quadratic_compactification,
      ``exists_simultaneous_retained_presentation,
      ``exists_fixed_bad_locus_retained_presentation,
      ``finiteProjectiveBaseRestriction_toSpec, ``finiteProjectiveBaseRestriction_map,
      ``retained_prescribed_boundary_on_base, ``quotient_retained_bad_cover,
      ``finiteProjectiveBaseRestriction_properties,
      ``finiteProjectiveBaseRestriction_retained_smooth] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original etale problem: actual retained presentation; standard axioms."
