/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.BoundaryEtaleExcision
public import Motivic.Cohomology.A1.PresheafBoundaryEtaleExcision

/-! # Original closed units in étale boundary excision

The existing excision isomorphisms are compared through their actual adjunction
units and the original direct-image composition isomorphism. This does not
replace the boundary map by an abstract isomorphism or assume a purity theorem.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteEtaleSite

section Units

variable {Z T S : Scheme.{u}} (i : Z ⟶ T) (p : T ⟶ S)
  (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})

/-- The original composition comparison is pinned by the genuine units. -/
@[reassoc]
theorem inverseImageCompIso_inv_unit :
    (imageAdjunction (i ≫ p)).unit.app G ≫
        (directImage (i ≫ p)).map ((inverseImageCompIso i p).inv.app G) ≫
        (directImageCompIso i p).inv.app ((inverseImage i).obj ((inverseImage p).obj G)) =
      (imageAdjunction p).unit.app G ≫
        (directImage p).map ((imageAdjunction i).unit.app ((inverseImage p).obj G)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (imageAdjunction (i ≫ p))
    (((imageAdjunction p).comp (imageAdjunction i)).ofNatIsoRight
      (directImageCompIso i p)) G
  change (imageAdjunction (i ≫ p)).unit.app G ≫
      (directImage (i ≫ p)).map ((inverseImageCompIso i p).inv.app G) = _ at h
  simp only [Adjunction.ofNatIsoRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app] at h
  have h' := congrArg (fun f => f ≫ (directImageCompIso i p).inv.app
    ((inverseImage i).obj ((inverseImage p).obj G))) h
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using h'

variable [Etale p] [IsSeparated p] [QuasiCompact p]

/-- Genuine inverse image and literal étale restriction have the same unit
under the specified left-adjoint comparison. -/
@[reassoc]
theorem inverseImageEtaleIso_unit :
    (imageAdjunction p).unit.app G ≫
        (directImage p).map ((inverseImageEtaleIso p).hom.app G) =
      (etaleRestrictionAdjunction p).unit.app G :=
  Adjunction.unit_leftAdjointUniq_hom_app (imageAdjunction p)
    (etaleRestrictionAdjunction p) G

/-- Any actual ambient comparison after étale restriction commutes with the
closed unit, including the original inverse/direct-image composition maps. -/
@[reassoc]
theorem inverseImageEtaleComparison_unit
    {H : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}}
    (e : (etaleRestriction p).obj G ⟶ H) :
    (imageAdjunction (i ≫ p)).unit.app G ≫
        (directImage (i ≫ p)).map
          ((inverseImageCompIso i p).inv.app G ≫
            (inverseImage i).map ((inverseImageEtaleIso p).hom.app G ≫ e)) ≫
        (directImageCompIso i p).inv.app ((inverseImage i).obj H) =
      (etaleRestrictionAdjunction p).unit.app G ≫
        (directImage p).map (e ≫ (imageAdjunction i).unit.app H) := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [(directImageCompIso i p).inv.naturality]
  change (imageAdjunction (i ≫ p)).unit.app G ≫
      (directImage (i ≫ p)).map ((inverseImageCompIso i p).inv.app G) ≫
      (directImageCompIso i p).inv.app ((inverseImage i).obj ((inverseImage p).obj G)) ≫
      (directImage p).map ((directImage i).map
        ((inverseImage i).map ((inverseImageEtaleIso p).hom.app G ≫ e))) = _
  rw [inverseImageCompIso_inv_unit_assoc, ← Functor.map_comp,
    ← (imageAdjunction i).unit.naturality]
  simp only [Functor.map_comp, Category.assoc]
  rw [inverseImageEtaleIso_unit_assoc]

end Units

section Boundary

variable {B : Scheme.{u}} {U Y U' Y' : SmoothSite B}
  (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
  [Etale p.left] [IsSeparated p.left] [QuasiCompact p.left]
  (hpb : IsPullback q j' j p) {Z : SmoothSite B} (i' : Z ⟶ Y')

/-- The existing sheaf-cokernel excision isomorphism preserves the original
closed unit, with the specified ambient cokernel comparison. -/
theorem boundaryEtaleExcisionIso_unit
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1}) :
    (imageAdjunction (i' ≫ p).left).unit.app (boundaryAmbientCokernel F j) ≫
        (directImage (i' ≫ p).left).map
          (boundaryEtaleExcisionIso F j p j' q hpb i').hom ≫
        (directImageCompIso i'.left p.left).inv.app (boundaryCokernel F j' i') =
      (etaleRestrictionAdjunction p.left).unit.app (boundaryAmbientCokernel F j) ≫
        (directImage p.left).map ((boundaryAmbientEtaleIso F j p j' q hpb).hom ≫
          (imageAdjunction i'.left).unit.app (boundaryAmbientCokernel F j')) := by
  simpa only [boundaryEtaleExcisionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc] using
    inverseImageEtaleComparison_unit i'.left p.left (boundaryAmbientCokernel F j)
      (boundaryAmbientEtaleIso F j p j' q hpb).hom

/-- The same unit identity for the original presheaf quotient, sheafified only
after taking its cokernel. -/
theorem presheafBoundaryEtaleExcisionIso_unit
    (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (imageAdjunction (i' ≫ p).left).unit.app (presheafBoundaryAmbient P j) ≫
        (directImage (i' ≫ p).left).map
          (presheafBoundaryEtaleExcisionIso P j p j' q hpb i').hom ≫
        (directImageCompIso i'.left p.left).inv.app (presheafBoundary P j' i') =
      (etaleRestrictionAdjunction p.left).unit.app (presheafBoundaryAmbient P j) ≫
        (directImage p.left).map ((presheafBoundaryAmbientEtaleIso P j p j' q hpb).hom ≫
          (imageAdjunction i'.left).unit.app (presheafBoundaryAmbient P j')) := by
  simpa only [presheafBoundaryEtaleExcisionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc] using
    inverseImageEtaleComparison_unit i'.left p.left (presheafBoundaryAmbient P j)
      (presheafBoundaryAmbientEtaleIso P j p j' q hpb).hom

end Boundary

end Motivic.FiniteEtaleSite
