/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.Boundary
/-! # The literal compact pencil of the two original neighborhood section pairs -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R) (l m : ℕ) (e : neighborhoodFrame R V r l)

/-- The tensor product of the pulled-back dual numerator twist and dual fixed Psi twist. -/
def commonNeighborhoodPencilLine : LineBundle (commonNeighborhoodAmbient R V r) :=
  tensorLineBundle _
    (pullbackLineBundle (commonNeighborhoodToSectionAmbient R V r)
      (dualLineBundle _ (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r)))))
    (pullbackLineBundle (commonNeighborhoodToPsiAmbient R V r)
      (dualLineBundle _ (fixedPsiTwistLine R r m)))

/-- The pencil functional formed from the graph-twisted normalized denominator and `t`. -/
def NeighborhoodSectionPair.pencilStart (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :
    (commonNeighborhoodPencilLine R V r l m).val ⟶
      SheafOfModules.unit (commonNeighborhoodAmbient R V r).ringCatSheaf :=
  mixedProductFunctional (commonNeighborhoodToSectionAmbient R V r)
    (commonNeighborhoodToPsiAmbient R V r)
    (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
      (dualLineBundle _ (neighborhoodLocalIdeal R V r))) (fixedPsiTwistLine R r m)
    (twistedIdealSection _ (neighborhoodLocalIdeal R V r) (neighborhoodLocalTwist R V r l)
      (neighborhoodLocalGraphFunctional R V r) d.normalizedDenominator) t

/-- The pencil functional formed from the normalized numerator and `n`. -/
def NeighborhoodSectionPair.pencilEnd (d : NeighborhoodSectionPair R V hV r l e)
    (n : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :
    (commonNeighborhoodPencilLine R V r l m).val ⟶
      SheafOfModules.unit (commonNeighborhoodAmbient R V r).ringCatSheaf :=
  mixedProductFunctional (commonNeighborhoodToSectionAmbient R V r)
    (commonNeighborhoodToPsiAmbient R V r)
    (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
      (dualLineBundle _ (neighborhoodLocalIdeal R V r))) (fixedPsiTwistLine R r m)
    d.normalizedNumerator n

lemma NeighborhoodSectionPair.pencil_boundary (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t)
      (commonNeighborhoodBoundaryMap R V r) =
    Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n)
      (commonNeighborhoodBoundaryMap R V r) :=
  (d.common_pencil_boundary R V hV r l m e n t hn).symm

lemma NeighborhoodSectionPair.pencilStart_boundary_isIso
    (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n)]
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    IsIso ((Scheme.Modules.pullback (commonNeighborhoodBoundaryMap R V r)).map
      (d.pencilStart R V hV r l m e t)) := by
  have he := d.common_product_unit R V hV r l m e n
  have hi : IsIso (Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t)
      (commonNeighborhoodBoundaryMap R V r)) := by
    rw [d.pencil_boundary R V hV r l m e n t hn]
    exact he
  exact (isIso_comp_right_iff _ (pullbackUnitIso (commonNeighborhoodBoundaryMap R V r)).hom).mp hi
end AlgebraicGeometry.RelativeProjectiveLine
