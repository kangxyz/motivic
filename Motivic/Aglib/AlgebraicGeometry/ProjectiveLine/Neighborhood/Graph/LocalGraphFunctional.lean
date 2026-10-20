module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.NormalizedPair
/-! # The literal canonical ideal functional on the original base-restricted curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
private lemma restrict_functional {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (a : M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (restrictFunctorIsoPullback j).hom.app M ≫ Scheme.Modules.Hom.pullbackToUnit a j =
      (restrictFunctor j).map a ≫ (restrictUnitIso j).hom := by
  unfold Scheme.Modules.Hom.pullbackToUnit
  rw [← (restrictFunctorIsoPullback j).hom.naturality_assoc]
  exact congrArg (fun f => (restrictFunctor j).map a ≫ f)
    (restrictFunctorIsoPullback_hom_unit j)
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)

/-- The graph ideal inclusion restricted to the section open, with target the unit sheaf. -/
def neighborhoodLocalGraphFunctional : (neighborhoodLocalIdeal R V r).val ⟶
    SheafOfModules.unit (neighborhoodSectionOpen R V r).toScheme.ringCatSheaf :=
  (restrictFunctor (neighborhoodSectionOpen R V r).ι).map
    (Scheme.Hom.idealInclusion (Scheme.Hom.compactificationGraph
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (neighborhoodInclusion R V))) ≫
    (restrictUnitIso (neighborhoodSectionOpen R V r).ι).hom

/-- This is the original ideal inclusion under native open pullback, not a chosen equation. -/
lemma neighborhoodLocalGraphFunctional_pullback :
    (restrictFunctorIsoPullback (neighborhoodSectionOpen R V r).ι).hom.app
      (neighborhoodGraphLine R V).val ≫
        Scheme.Modules.Hom.pullbackToUnit
          (Scheme.Hom.idealInclusion (Scheme.Hom.compactificationGraph
            (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (neighborhoodInclusion R V)))
          (neighborhoodSectionOpen R V r).ι = neighborhoodLocalGraphFunctional R V r :=
  restrict_functional _ _
end AlgebraicGeometry.RelativeProjectiveLine
