module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.OpenPair
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.FiniteFlat
/-! # Constructed relative diagonal sections with whole finite flat zero schemes -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable {r : R} {n : ℕ} {e : neighborhoodFrame R V r n}

lemma NeighborhoodSectionPair.numerator_finite_flat
    (d : NeighborhoodSectionPair R V hV r n e) :
    NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
      (neighborhoodSerreOpen_eq_compact R V r)
      (neighborhoodRestrictLineBundle R V (neighborhoodNumeratorLine R V n)
        (neighborhoodSectionOpen R V r)) d.numeratorHom := by
  have := d.numeratorHom_boundary_isIso
  exact neighborhoodOpenSection_finite_flat R V hV r (neighborhoodSectionOpen R V r)
    (neighborhoodSerreOpen_eq_compact R V r)
    (neighborhoodRestrictLineBundle R V (neighborhoodNumeratorLine R V n)
      (neighborhoodSectionOpen R V r)) d.numeratorHom

lemma NeighborhoodSectionPair.denominator_finite_flat
    (d : NeighborhoodSectionPair R V hV r n e) :
    NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
      (neighborhoodSerreOpen_eq_compact R V r)
      (neighborhoodRestrictLineBundle R V (neighborhoodDenominatorLine R V n)
        (neighborhoodSectionOpen R V r)) d.denominatorHom := by
  have := d.denominatorHom_boundary_isIso
  exact neighborhoodOpenSection_finite_flat R V hV r (neighborhoodSectionOpen R V r)
    (neighborhoodSerreOpen_eq_compact R V r)
    (neighborhoodRestrictLineBundle R V (neighborhoodDenominatorLine R V n)
      (neighborhoodSectionOpen R V r)) d.denominatorHom

/-- Both sections, their literal prescribed boundary equations, and full finite-flat zero data
are produced from Serre vanishing on the same original base shrink. -/
theorem exists_neighborhoodFiniteFlatSectionPair [IsNoetherianRing R] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : R, ∀ e : neighborhoodFrame R V r n,
      ∃ d : NeighborhoodSectionPair R V hV r n e,
        NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
          (neighborhoodSerreOpen_eq_compact R V r)
          (neighborhoodRestrictLineBundle R V (neighborhoodNumeratorLine R V n)
            (neighborhoodSectionOpen R V r)) d.numeratorHom ∧
        NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
          (neighborhoodSerreOpen_eq_compact R V r)
          (neighborhoodRestrictLineBundle R V (neighborhoodDenominatorLine R V n)
            (neighborhoodSectionOpen R V r)) d.denominatorHom := by
  obtain ⟨N, hN⟩ := exists_neighborhoodSectionPair R V hV
  refine ⟨N, fun n hn r e => ?_⟩
  obtain ⟨d⟩ := hN n hn r e
  exact ⟨d, d.numerator_finite_flat R V hV, d.denominator_finite_flat R V hV⟩
/-- Around any original base point, the frames and both finite-flat sections are constructed. -/
theorem exists_neighborhoodFiniteFlatSectionPair_near [IsNoetherianRing R]
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∃ e : (n : ℕ) → neighborhoodFrame R V r n,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ d : NeighborhoodSectionPair R V hV r n (e n),
        NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
          (neighborhoodSerreOpen_eq_compact R V r)
          (neighborhoodRestrictLineBundle R V (neighborhoodNumeratorLine R V n)
            (neighborhoodSectionOpen R V r)) d.numeratorHom ∧
        NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
          (neighborhoodSerreOpen_eq_compact R V r)
          (neighborhoodRestrictLineBundle R V (neighborhoodDenominatorLine R V n)
            (neighborhoodSectionOpen R V r)) d.denominatorHom := by
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_fullBoundary_principal_positiveTwist_unitIso R V hV s
  obtain ⟨N, hN⟩ := exists_neighborhoodFiniteFlatSectionPair R V hV
  exact ⟨r, hr, e, N, fun n hn => hN n hn r (e n)⟩
end AlgebraicGeometry.RelativeProjectiveLine
