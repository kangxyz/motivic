module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.Twist
/-! # Native Serre twist units on the actual graph boundary over the common base shrink -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R)

abbrev neighborhoodSerreTwist (n : ℕ) :=
  (Scheme.Modules.pullback (neighborhoodProjectiveIso R V).hom).obj
    (ProjectiveSpace.twistingSheaf Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ))

/-- The native relative twist, restricted to precisely the full graph boundary over D(r). -/
def neighborhoodGraphRelativeBoundaryTwistIso (n : ℕ)
    (e : (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
      (neighborhoodSerreTwist R V n)).restrict (neighborhoodGraphBoundaryOpen R V hV r).ι ≅
        SheafOfModules.unit (neighborhoodGraphBoundaryOpen R V hV r).toScheme.ringCatSheaf :=
  (restrictFunctorIsoPullback (neighborhoodGraphBoundaryOpen R V hV r).ι).app _ ≪≫
    (Scheme.Modules.pullback (neighborhoodGraphBoundaryOpen R V hV r).ι).mapIso
      ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).mapIso
        (neighborhoodOriginalTwistIso R V (n : ℤ))) ≪≫
    (pullbackComp (neighborhoodGraphBoundaryOpen R V hV r).ι
      (neighborhoodGraphBoundaryMap R V hV)).app _ ≪≫
    (pullbackComp ((neighborhoodGraphBoundaryOpen R V hV r).ι ≫
      neighborhoodGraphBoundaryMap R V hV) (pullback.snd _ _)).app _ ≪≫
    (pullbackCongr (Category.assoc _ _ _)).app _ ≪≫
    neighborhoodGraphOriginalBoundaryTwistIso R V hV r n e

/-- No unit hypothesis: one actual base neighborhood trivializes all native Serre twists. -/
theorem exists_neighborhoodGraphRelativeBoundaryTwists (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧ Nonempty ((n : ℕ) →
      ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
        (neighborhoodSerreTwist R V n)).restrict (neighborhoodGraphBoundaryOpen R V hV r).ι ≅
          SheafOfModules.unit (neighborhoodGraphBoundaryOpen R V hV r).toScheme.ringCatSheaf) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_fullBoundary_principal_positiveTwist_unitIso R V hV s
  exact ⟨r, hr, ⟨fun n => neighborhoodGraphRelativeBoundaryTwistIso R V hV r n (e n)⟩⟩
end AlgebraicGeometry.RelativeProjectiveLine
