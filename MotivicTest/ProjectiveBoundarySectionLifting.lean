import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.BoundarySectionLifting

/-! Consumer checks for genuine full closed-boundary lifting after projective twist. -/

set_option linter.hashCommand false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

-- Genuine full closed-boundary lifting on the projective line.
-- No Cartier, invertible-kernel, UFD, smoothness or reduced-boundary hypothesis.
example (R : Type) [CommRing R] [IsNoetherianRing R]
    {Z : Scheme} (i : Z ⟶ ProjectiveSpace R (Fin 2)) [IsClosedImmersion i]
    (M : (ProjectiveSpace R (Fin 2)).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R (Fin 2)) M) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      Function.Surjective ((projectiveBoundaryRestriction R (Fin 2) i M d).app ⊤) :=
  projectiveBoundaryRestriction_eventually_surjective R (Fin 2) 1 (Equiv.refl _) i M hM

#print axioms projective_coherentQuotient_eventually_sections_surjective
#print axioms projectiveBoundaryRestriction_eventually_surjective
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackPushforwardUnit_epi_of_closedImmersion
