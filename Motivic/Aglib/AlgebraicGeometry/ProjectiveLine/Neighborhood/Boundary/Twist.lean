/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.Projection
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ProjectiveMap
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.RelativeNeighborhood
/-! # Common original-boundary twist units on the actual neighborhood graph -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens)
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R)

/-- The inverse image of the base principal open defined by `r` on the graph boundary. -/
abbrev neighborhoodGraphBoundaryOpen :=
  (neighborhoodGraphBoundaryToOriginal R V hV ≫ fullBoundaryStructure R V) ⁻¹ᵁ
    PrimeSpectrum.basicOpen r

/-- Restrict only by the common original base neighborhood. -/
def neighborhoodGraphBoundaryPrincipalMap :
    (neighborhoodGraphBoundaryOpen R V hV r).toScheme ⟶
      (fullBoundaryPrincipalOpen R V r).toScheme :=
  IsOpenImmersion.lift (fullBoundaryPrincipalOpen R V r).ι
    ((neighborhoodGraphBoundaryOpen R V hV r).ι ≫
      neighborhoodGraphBoundaryToOriginal R V hV) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        exact x.property)

@[reassoc (attr := simp)]
lemma neighborhoodGraphBoundaryPrincipalMap_ι :
    neighborhoodGraphBoundaryPrincipalMap R V hV r ≫ (fullBoundaryPrincipalOpen R V r).ι =
      (neighborhoodGraphBoundaryOpen R V hV r).ι ≫
        neighborhoodGraphBoundaryToOriginal R V hV := IsOpenImmersion.lift_fac _ _ _

lemma neighborhoodGraphBoundaryPrincipalMap_target :
    (neighborhoodGraphBoundaryOpen R V hV r).ι ≫ neighborhoodGraphBoundaryMap R V hV ≫
      pullback.snd _ _ =
    neighborhoodGraphBoundaryPrincipalMap R V hV r ≫
      (fullBoundaryPrincipalOpen R V r).ι ≫ fullNeighborhoodBoundaryMap R V := by
  simp only [neighborhoodGraphBoundaryPrincipalMap_ι_assoc,
    neighborhoodGraphBoundaryToOriginal_fac]

/-- Pulling the same original boundary frame gives the actual graph-boundary frame. -/
def neighborhoodGraphOriginalBoundaryTwistIso (n : ℕ)
    (e : (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    (Scheme.Modules.pullback ((neighborhoodGraphBoundaryOpen R V hV r).ι ≫
      neighborhoodGraphBoundaryMap R V hV ≫ pullback.snd _ _)).obj
        (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
      SheafOfModules.unit (neighborhoodGraphBoundaryOpen R V hV r).toScheme.ringCatSheaf :=
  (pullbackCongr (neighborhoodGraphBoundaryPrincipalMap_target R V hV r)).app _ ≪≫
    (pullbackComp (neighborhoodGraphBoundaryPrincipalMap R V hV r)
      ((fullBoundaryPrincipalOpen R V r).ι ≫ fullNeighborhoodBoundaryMap R V)).symm.app _ ≪≫
    (Scheme.Modules.pullback (neighborhoodGraphBoundaryPrincipalMap R V hV r)).mapIso e ≪≫
    pullbackUnitIso _

/-- One original base shrink produces every positive graph-boundary twist frame. -/
theorem exists_neighborhoodGraphBoundaryTwists (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧ Nonempty ((n : ℕ) →
      (Scheme.Modules.pullback ((neighborhoodGraphBoundaryOpen R V hV r).ι ≫
        neighborhoodGraphBoundaryMap R V hV ≫ pullback.snd _ _)).obj
          (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (neighborhoodGraphBoundaryOpen R V hV r).toScheme.ringCatSheaf) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_fullBoundary_principal_positiveTwist_unitIso R V hV s
  exact ⟨r, hr, ⟨fun n => neighborhoodGraphOriginalBoundaryTwistIso R V hV r n (e n)⟩⟩
end AlgebraicGeometry.RelativeProjectiveLine
