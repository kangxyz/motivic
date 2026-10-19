module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ProjectiveMap
/-! Native projective presentation and same-target-twist consumer. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example : IsFinite (neighborhoodProjectiveIso R V).hom := inferInstance
example (n : ℤ) : Nonempty (
    (Scheme.Modules.pullback (neighborhoodProjectiveIso R V).hom).obj
      (ProjectiveSpace.twistingSheaf Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) n) ≅
    (Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (neighborhoodProjection R V)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) n)) :=
  ⟨neighborhoodOriginalTwistIso R V n⟩
#print axioms neighborhoodProjectiveIso
#print axioms neighborhoodOriginalTwistIso
