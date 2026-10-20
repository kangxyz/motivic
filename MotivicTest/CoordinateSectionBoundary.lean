module
import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ProjectiveLine.CoordinateSection.Boundary
/-! The original coordinate ideal is canonically a unit on the whole missing boundary. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable {R A : Type u} [CommRing R] [CommRing A]
variable (V : (Spec (.of (Polynomial R))).Opens) (z : Polynomial R →+* A)
variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom z))]
example (hz : Set.range (Spec.map (CommRingCat.ofHom z)) ⊆ V) :
    IsIso (Scheme.Modules.Hom.pullbackToUnit
      (Scheme.Hom.idealInclusion (coordinateSection A (z Polynomial.X)))
      (missingBoundaryMap V z)) :=
  coordinateSection_missing_idealInclusion_isIso V z hz
example (hz : Set.range (Spec.map (CommRingCat.ofHom z)) ⊆ V) :
    (coordinateSectionMissingIdealIso V z hz).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Hom.idealInclusion (coordinateSection A (z Polynomial.X)))
        (missingBoundaryMap V z) = 𝟙 _ :=
  coordinateSection_missing_idealIso_inclusion V z hz
#print axioms coordinateSection_missing_idealInclusion_isIso
#print axioms coordinateSection_missing_idealIso_inclusion
