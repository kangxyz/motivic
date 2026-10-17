module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodSerreSectionPair
/-! Actual graph numerator and denominator are produced on the common base shrink. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
attribute [local instance] neighborhoodGraphBoundary_closed
example : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : R,
    ∀ e : (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf,
    ∃ b : Γ((Scheme.Modules.pushforward (neighborhoodProjectiveIso R V).hom).obj
      ((moduleTensorLeftFunctor (neighborhoodGraphAmbient R V)
        (neighborhoodSerreTwist R V n)).obj
          (SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf)),
        neighborhoodSerreOpen R V r),
      ((Scheme.Modules.pushforward (neighborhoodProjectiveIso R V).hom).map
        (Scheme.CoherentGraph.boundaryRestriction (neighborhoodGraphBoundaryMap R V hV)
          (neighborhoodSerreTwist R V n)
          (SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf))).app
            (neighborhoodSerreOpen R V r) b = neighborhoodBoundaryUnitSection R V hV r n e := by
  obtain ⟨N, hN⟩ := exists_neighborhoodSerreSectionPair R V hV
  refine ⟨N, fun n hn r e => ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hN n hn r e
  exact ⟨b, hb⟩
#print axioms exists_neighborhoodSerreSectionPair
#print axioms neighborhoodBoundaryCoefficientIso
