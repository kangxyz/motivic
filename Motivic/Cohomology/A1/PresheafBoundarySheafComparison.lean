/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafBoundaryCokernel
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The original-presheaf boundary of a sheaf agrees with its sheaf boundary -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

variable {B : Scheme.{u}} (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B}

/-- Sheafifying the original neighborhood quotient of a sheaf gives its actual
ambient sheaf cokernel. The comparison is induced by the sheafification counits. -/
def presheafBoundaryAmbientSheafIso (j : U ⟶ Y) :
    presheafBoundaryAmbient F.obj j ≅ boundaryAmbientCokernel F j :=
  let r := restrictionToDirectImage F j
  let L := presheafToSheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1}
  let adj := sheafificationAdjunction (nisnevichTopology Y.left) AddCommGrpCat.{u + 1}
  PreservesCokernel.iso L r.hom ≪≫
    cokernel.mapIso (L.map r.hom) r
      (asIso (adj.counit.app ((restrict Y AddCommGrpCat).obj F)))
      (asIso (adj.counit.app ((directImage j.left).obj ((restrict U AddCommGrpCat).obj F))))
      (adj.counit.naturality r)

/-- The comparison preserves the original punctured-section projection, not just
its target up to an unspecified isomorphism. -/
@[reassoc (attr := simp)]
theorem presheafBoundaryProjection_sheafIso (j : U ⟶ Y) :
    presheafBoundaryProjection F.obj j ≫ (presheafBoundaryAmbientSheafIso F j).hom.hom =
      (cokernel.π (restrictionToDirectImage F j)).hom := by
  let r := restrictionToDirectImage F j
  let J := nisnevichTopology Y.left
  let L := presheafToSheaf J AddCommGrpCat.{u + 1}
  let adj := sheafificationAdjunction J AddCommGrpCat.{u + 1}
  let Q := (directImage j.left).obj ((restrict U AddCommGrpCat).obj F)
  have h : L.map (cokernel.π r.hom) ≫ (presheafBoundaryAmbientSheafIso F j).hom =
      adj.counit.app Q ≫ cokernel.π r := by
    dsimp only [L, r, J, adj, Q]
    simp only [presheafBoundaryAmbientSheafIso, Iso.trans_hom,
      PreservesCokernel.π_iso_hom_assoc, cokernel.mapIso_hom, cokernel.map,
      cokernel.π_desc, asIso_hom]
  change (cokernel.π r.hom ≫ toSheafify J _) ≫
    (presheafBoundaryAmbientSheafIso F j).hom.hom = (cokernel.π r).hom
  rw [toSheafify_naturality, Category.assoc]
  change toSheafify J _ ≫
      (L.map (cokernel.π r.hom) ≫ (presheafBoundaryAmbientSheafIso F j).hom).hom = _
  rw [h]
  change toSheafify J Q.obj ≫ (adj.counit.app Q).hom ≫ (cokernel.π r).hom = _
  have ht : toSheafify J Q.obj ≫ (adj.counit.app Q).hom = 𝟙 Q.obj :=
    adj.right_triangle_components Q
  rw [← Category.assoc, ht, Category.id_comp]

/-- Applying the actual closed inverse-image functor to the ambient comparison
identifies the two boundary constructions for an original coefficient sheaf. -/
def presheafBoundarySheafIso (j : U ⟶ Y) (i : Z ⟶ Y) :
    presheafBoundary F.obj j i ≅ boundaryCokernel F j i :=
  (inverseImage i.left).mapIso (presheafBoundaryAmbientSheafIso F j)

end Motivic.FiniteEtaleSite
