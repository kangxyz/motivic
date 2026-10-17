module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodRetainedSectionChange
/-! # Actual retained factor spans under the common source change -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelativeProjectiveLine

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R) :
    IsPullback (commonNeighborhoodRetainedToPsi R V r)
      (pullback.fst (commonNeighborhoodProjection R V r)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))))
      (pullback.fst (fixedPsiProjection R r)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))))
      (commonNeighborhoodToPsi R V r) :=
  commonNeighborhoodRetainedToPsi_isPullback R V r

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)
    [IsAffine V.toScheme] (r : R) :
    IsPullback (commonNeighborhoodRetainedToSection R V r)
      (pullback.fst (commonNeighborhoodProjection R V r)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))))
      ((neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r) ≫
        commonNeighborhoodSectionProjection R V r)
      (commonNeighborhoodToSectionSource R V r) :=
  commonNeighborhoodRetainedToSection_source_isPullback R V r

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)
    [IsAffine V.toScheme] (r : R) :
    commonNeighborhoodRetainedToSection R V r ≫
      (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι ≫
        pullback.snd (neighborhoodProjection R V)
          ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) =
      pullback.snd (commonNeighborhoodProjection R V r)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) :=
  commonNeighborhoodRetainedToSection_target R V r
