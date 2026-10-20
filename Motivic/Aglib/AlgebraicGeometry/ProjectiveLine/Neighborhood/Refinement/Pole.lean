module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.FiniteFlatPencil
/-! # The actual denominator product has a finite-flat whole retained zero scheme -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R) (l m : ℕ) (e : neighborhoodFrame R V r l)

private lemma pulled_section_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (a : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    [IsIso (pullbackSectionMap g a)] : IsIso (pullbackSectionMap (f ≫ g) a) := by
  rw [← pullbackSectionMap_comp f g a]
  have : IsIso (pullbackSectionMap f (pullbackSectionMap g a)) := by
    change IsIso ((pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (pullbackSectionMap g a))
    infer_instance
  infer_instance

/-- The tensor product of the pulled-back dual local twist and dual fixed Psi twist. -/
def commonNeighborhoodPoleLine : LineBundle (commonNeighborhoodAmbient R V r) :=
  tensorLineBundle _
    (pullbackLineBundle (commonNeighborhoodToSectionAmbient R V r)
      (dualLineBundle _ (neighborhoodLocalTwist R V r l)))
    (pullbackLineBundle (commonNeighborhoodToPsiAmbient R V r)
      (dualLineBundle _ (fixedPsiTwistLine R r m)))

/-- The pole functional formed from the normalized denominator and `t`. -/
def NeighborhoodSectionPair.poleFunctional (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :
    (commonNeighborhoodPoleLine R V r l m).val ⟶
      SheafOfModules.unit (commonNeighborhoodAmbient R V r).ringCatSheaf :=
  mixedProductFunctional (commonNeighborhoodToSectionAmbient R V r)
    (commonNeighborhoodToPsiAmbient R V r)
    (neighborhoodLocalTwist R V r l) (fixedPsiTwistLine R r m) d.normalizedDenominator t

lemma NeighborhoodSectionPair.pole_boundary_unit (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) t)] :
    IsIso (Scheme.Modules.Hom.pullbackToUnit (d.poleFunctional R V hV r l m e t)
      (commonNeighborhoodBoundaryMap R V r)) := by
  have hb : IsIso (pullbackSectionMap
      (commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToSectionAmbient R V r)
      d.normalizedDenominator) := by
    rw [← commonNeighborhoodBoundaryToSection_fac R V r hV]
    have := d.normalizedDenominator_boundary_isIso
    exact pulled_section_unit _ _ _
  have := common_psi_unit R V r m t
  exact mixedProductFunctional_boundary_isIso (commonNeighborhoodToSectionAmbient R V r)
    (commonNeighborhoodToPsiAmbient R V r) (commonNeighborhoodBoundaryMap R V r)
    (neighborhoodLocalTwist R V r l) (fixedPsiTwistLine R r m) d.normalizedDenominator t

lemma NeighborhoodSectionPair.pole_finite_mono_flat (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) t)] :
    let j := commonNeighborhoodRetainedInclusion R V r
    let q := pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _)
    let a := Scheme.Modules.Hom.pullbackToUnit (d.poleFunctional R V hV r l m e t) j
    IsFinite (Scheme.Modules.Hom.zeroInclusion a ≫ j ≫ q) ∧
      Mono a ∧ Flat (Scheme.Modules.Hom.zeroInclusion a ≫ j ≫ q) := by
  have := commonNeighborhoodSource_affine R V r
  have := commonNeighborhoodRetainedCurve_affine R V r
  have := commonNeighborhoodRetainedCurve_smooth R V r
  have hi := d.pole_boundary_unit R V hV r l m e t
  have : IsIso ((Scheme.Modules.pullback (commonNeighborhoodBoundaryMap R V r)).map
      (d.poleFunctional R V hV r l m e t)) :=
    (isIso_comp_right_iff _ (pullbackUnitIso (commonNeighborhoodBoundaryMap R V r)).hom).mp hi
  have hp := GlobalBoundaryPencil.pencil_finite_flat_on_open
    (commonNeighborhoodBoundaryMap R V r)
    (pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))
    (commonNeighborhoodRetainedInclusion R V r) (commonNeighborhoodPoleLine R V r l m)
    (d.poleFunctional R V hV r l m e t) (d.poleFunctional R V hV r l m e t) 0 rfl
    (commonNeighborhoodRetained_boundary_cover R V r)
  rw [GlobalBoundaryPencil.pencil_zero] at hp
  exact hp
end AlgebraicGeometry.RelativeProjectiveLine
