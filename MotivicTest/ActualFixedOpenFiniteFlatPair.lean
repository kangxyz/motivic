module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.FixedOpen.FiniteFlatPair
/-! # Actual fixed-source psi pairs have no compactification or unit premise -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (a : Spec (.of R) ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion a]
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    (h : Disjoint (Set.range a) (Set.range (Scheme.Hom.boundaryCoordinateMap k B z)))
    [IsClosedImmersion (Scheme.Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Scheme.Hom.boundaryCoordinateMap k B z ≫ Scheme.Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = Scheme.Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) p (Scheme.Hom.boundaryCoordinateMap k B z))
    (U : (Spec (.of (Polynomial k))).Opens)
    (hz : Set.range (Scheme.Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    ∃ d : ℕ,
      ∃ n t : SheafOfModules.unit (fixedAmbient k p a).ringCatSheaf ⟶
        (Scheme.Modules.Invertible.tensorLineBundle (fixedAmbient k p a)
          (fixedTwistBundle k p a d) (actualUnitBundle (fixedAmbient k p a))).val,
      FixedRetainedSectionFiniteFlat k p a U
        (Scheme.Modules.Invertible.tensorLineBundle _ (fixedTwistBundle k p a d)
          (actualUnitBundle _)) n ∧
      FixedRetainedSectionFiniteFlat k p a U
        (Scheme.Modules.Invertible.tensorLineBundle _ (fixedTwistBundle k p a d)
          (actualUnitBundle _)) t := by
  obtain ⟨N, hN⟩ := exists_actualFixedOpenFiniteFlatSectionPair k p a B z h s hs H U hz
  obtain ⟨u, hu, n, t, hn, ht, hIn, hIt, hFn, hFt⟩ := hN N le_rfl
  exact ⟨N, n, t, hFn, hFt⟩

open Lean in
run_cmd do
  for name in #[``fixedBoundary_closed, ``fixedFieldBoundary_finite,
      ``fixedBoundaryUnit_infinity, ``fixedBoundaryUnit_coordinate,
      ``exists_actualFixedOpenFiniteFlatSectionPair] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual fixed-source psi pair uses only standard foundations."
