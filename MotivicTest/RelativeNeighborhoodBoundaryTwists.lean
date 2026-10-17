module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.RelativeNeighborhoodBoundaryTwists

/-! # Relative whole-boundary twist consumers without a field hypothesis -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.RelativeProjectiveLine
open AlgebraicGeometry.Scheme.Modules

universe u

namespace MotivicTest.RelativeNeighborhoodBoundaryTwists

variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)

/-- The base point is retained and one principal shrink supports all twist degrees. -/
theorem one_shrink_all_degrees
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      Nonempty ((n : ℕ) →
        (Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
          fullNeighborhoodBoundaryMap R V)).obj
          (twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
          SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :=
  exists_fullBoundary_principal_positiveTwist_unitIso R V hV s

variable (r : R) {A : Type u} [CommRing A]
  (b : Spec (.of A) ⟶ Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r))
  (e : (n : ℕ) →
    (Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
      fullNeighborhoodBoundaryMap R V)).obj
      (twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
      SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf)

/-- The affine source and the whole original boundary product are unchanged. -/
def native_relative_twist_unit (n : ℕ) :
    (Modules.pullback (boundaryRelativeMap R V r b)).obj
      (twistingSheaf A (ULift.{u} (Fin 2)) (n : ℤ)) ≅
      SheafOfModules.unit
        (pullback (sourceMap R r b) (fullNeighborhoodBoundaryMap R V ≫
          toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf :=
  fullBoundaryRelativeTwistIso R V r b e n

/-- The original section-producer coefficient has an actual global generator. -/
theorem original_coefficient_generator {C : Scheme.{u}}
    (a : C ⟶ ProjectiveSpace A (ULift.{u} (Fin 2)))
    (z : fullBoundarySource R V r b ⟶ C) (ha : z ≫ a = boundaryRelativeMap R V r b)
    (n : ℕ) :
    IsIso ((unitHomGlobalSectionsEquiv (fullBoundarySource R V r b)
      (fullBoundaryRelativeCoefficient R V r b a z n)).symm
        (fullBoundaryRelativeCoefficientUnitSection R V r b e a z ha n)) :=
  fullBoundaryRelativeCoefficientUnitSection_isIso R V r b e a z ha n

end MotivicTest.RelativeNeighborhoodBoundaryTwists
