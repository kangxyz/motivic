/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.SectionMaps
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.NormalizedPair
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Sections.NormalizedPair
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.MixedProductBoundaryPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionPullback
/-! # The actual common compact numerator product is a full-boundary unit -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
private lemma section_unit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (a : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    [IsIso (pullbackSectionMap g a)] : IsIso (pullbackSectionMap (f ≫ g) a) := by
  rw [← pullbackSectionMap_comp f g a]
  have : IsIso (pullbackSectionMap f (pullbackSectionMap g a)) := by
    change IsIso ((pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (pullbackSectionMap g a))
    infer_instance
  infer_instance
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R) (n m : ℕ) (e : neighborhoodFrame R V r n)

lemma NeighborhoodSectionPair.common_numerator_unit (d : NeighborhoodSectionPair R V hV r n e) :
    IsIso (pullbackSectionMap
      (commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToSectionAmbient R V r)
        d.normalizedNumerator) := by
  rw [← commonNeighborhoodBoundaryToSection_fac R V r hV]
  have := d.normalizedNumerator_boundary_isIso
  exact section_unit_comp (commonNeighborhoodBoundaryToSection R V r hV)
    (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r) d.normalizedNumerator

omit [IsAffine V.toScheme] in
lemma common_psi_unit
    (a : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶ (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) a)] :
    IsIso (pullbackSectionMap
      (commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToPsiAmbient R V r) a) := by
  rw [← commonNeighborhoodBoundaryToPsi_fac R V r]
  exact section_unit_comp (commonNeighborhoodBoundaryToPsi R V r) (fixedPsiBoundaryMap R r V) a

lemma NeighborhoodSectionPair.common_product_unit (d : NeighborhoodSectionPair R V hV r n e)
    (a : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶ (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) a)] :
    IsIso (Scheme.Modules.Hom.pullbackToUnit
      (mixedProductFunctional (commonNeighborhoodToSectionAmbient R V r)
        (commonNeighborhoodToPsiAmbient R V r)
        (tensorLineBundle _ (neighborhoodLocalTwist R V r n)
          (dualLineBundle _ (neighborhoodLocalIdeal R V r)))
        (fixedPsiTwistLine R r m) d.normalizedNumerator a)
      (commonNeighborhoodBoundaryMap R V r)) := by
  have := d.common_numerator_unit R V hV r n e
  have := common_psi_unit R V r m a
  exact mixedProductFunctional_boundary_isIso (commonNeighborhoodToSectionAmbient R V r)
    (commonNeighborhoodToPsiAmbient R V r) (commonNeighborhoodBoundaryMap R V r)
    (tensorLineBundle _ (neighborhoodLocalTwist R V r n)
      (dualLineBundle _ (neighborhoodLocalIdeal R V r)))
    (fixedPsiTwistLine R r m) d.normalizedNumerator a
end AlgebraicGeometry.RelativeProjectiveLine
