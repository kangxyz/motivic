module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.FiniteFlatPair
/-! Actual prescribed sections give whole finite flat zero schemes. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : R, ∀ e : neighborhoodFrame R V r n,
      ∃ d : NeighborhoodSectionPair R V hV r n e,
        NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
          (neighborhoodSerreOpen_eq_compact R V r)
          (neighborhoodRestrictLineBundle R V (neighborhoodNumeratorLine R V n)
            (neighborhoodSectionOpen R V r)) d.numeratorHom := by
  obtain ⟨N, hN⟩ := exists_neighborhoodFiniteFlatSectionPair R V hV
  exact ⟨N, fun n hn r e => by
    obtain ⟨d, ha, _⟩ := hN n hn r e
    exact ⟨d, ha⟩⟩
#print axioms exists_neighborhoodFiniteFlatSectionPair
#print axioms NeighborhoodSectionPair.numeratorHom_boundary_isIso
#print axioms NeighborhoodSectionPair.denominatorHom_boundary_isIso
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∃ e : (n : ℕ) → neighborhoodFrame R V r n,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nonempty (NeighborhoodSectionPair R V hV r n (e n)) := by
  obtain ⟨r, hr, e, N, hN⟩ := exists_neighborhoodFiniteFlatSectionPair_near R V hV s
  exact ⟨r, hr, e, N, fun n hn => by
    obtain ⟨d, _, _⟩ := hN n hn
    exact ⟨d⟩⟩
#print axioms exists_neighborhoodFiniteFlatSectionPair_near
