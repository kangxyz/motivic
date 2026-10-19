/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.WholeTarget

/-! # The original marked lift in the coefficient-restricted compactification

Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.MarkedDiagram`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.MarkedBaseChange`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundaryBaseSectionData`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C D : Scheme.{u}}
  (q : X ⟶ S) (p : Y ⟶ X) (π : C ⟶ S) (j : Y ⟶ C)
  (hq : j ≫ π = p ≫ q) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (U : X.Opens) (O : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ O → z t ∈ U)

/-- The marked support has the same original coefficient inverse image in both diagrams. -/
def boundaryBaseMarkedOpenIso :
    (boundaryBaseClosedOpen q z O).toScheme ≅ (((s ≫ j) ≫ π) ⁻¹ᵁ O).toScheme :=
  Z.isoOfEq (by
    change (z ≫ q) ⁻¹ᵁ O = ((s ≫ j) ≫ π) ⁻¹ᵁ O
    rw [Category.assoc, hq, ← Category.assoc, hs])

@[reassoc (attr := simp)]
theorem boundaryBaseMarkedOpenIso_hom_ι :
    (boundaryBaseMarkedOpenIso q p π j hq z s hs O).hom ≫
      (s ⁻¹ᵁ (j ⁻¹ᵁ (π ⁻¹ᵁ O))).ι = (boundaryBaseClosedOpen q z O).ι :=
  Scheme.isoOfEq_hom_ι _ _

/-- The existing actual marked lift lands in the original restricted compactification. -/
@[reassoc]
theorem boundaryBaseCoverLift_comp_inclusion :
    boundaryBaseCoverLift q p z s hs U O h ≫
      boundaryBaseCoverInclusion q p π j hq U O =
    (boundaryBaseMarkedOpenIso q p π j hq z s hs O).hom ≫
      boundaryBaseWholeMap π (s ≫ j) O := by
  rw [← cancel_mono (pullback.snd O.ι π)]
  simp only [Category.assoc, boundaryBaseCoverInclusion_snd,
    boundaryBaseCoverLift_ι_assoc, boundaryBaseWholeMap_snd, comp_preimage,
    boundaryBaseMarkedOpenIso_hom_ι_assoc]

/-- The full boundary uses the same infinity summand and this same marked-open iso. -/
def boundaryBaseFullMarkedIso (d : D ⟶ C) :
    (((d ≫ π) ⁻¹ᵁ O).toScheme ⨿ (boundaryBaseClosedOpen q z O).toScheme) ≅
      (((d ≫ π) ⁻¹ᵁ O).toScheme ⨿ (((s ≫ j) ≫ π) ⁻¹ᵁ O).toScheme) :=
  coprod.mapIso (Iso.refl _) (boundaryBaseMarkedOpenIso q p π j hq z s hs O)

/-- Literal full-boundary map equality, not merely support containment. -/
@[reassoc]
theorem boundaryBaseFullMarkedIso_hom_map (d : D ⟶ C) :
    (boundaryBaseFullMarkedIso q p π j hq z s hs O d).hom ≫
      coprod.desc (boundaryBaseWholeMap π d O) (boundaryBaseWholeMap π (s ≫ j) O) =
      coprod.desc (boundaryBaseWholeMap π d O)
        (boundaryBaseCoverLift q p z s hs U O h ≫
          boundaryBaseCoverInclusion q p π j hq U O) := by
  apply coprod.hom_ext
  · simp [boundaryBaseFullMarkedIso]
  · simp only [boundaryBaseFullMarkedIso, coprod.mapIso_hom, coprod.inr_map_assoc,
      coprod.inr_desc]
    exact (boundaryBaseCoverLift_comp_inclusion q p π j hq z s hs U O h).symm

/-- Transport the same full-boundary frame to the actual restricted marked diagram. -/
def boundaryBaseFullMarkedFrame (d : D ⟶ C)
    (M : (boundaryBaseCompactification π O).Modules)
    (e : (Modules.pullback
      (coprod.desc (boundaryBaseWholeMap π d O) (boundaryBaseWholeMap π (s ≫ j) O))).obj M ≅
        SheafOfModules.unit
          ((((d ≫ π) ⁻¹ᵁ O).toScheme ⨿ (((s ≫ j) ≫ π) ⁻¹ᵁ O).toScheme)).ringCatSheaf) :
    (Modules.pullback
      (coprod.desc (boundaryBaseWholeMap π d O)
        (boundaryBaseCoverLift q p z s hs U O h ≫
          boundaryBaseCoverInclusion q p π j hq U O))).obj M ≅
      SheafOfModules.unit
        ((((d ≫ π) ⁻¹ᵁ O).toScheme ⨿ (boundaryBaseClosedOpen q z O).toScheme)).ringCatSheaf := by
  rw [← boundaryBaseFullMarkedIso_hom_map q p π j hq z s hs U O h d]
  exact (Modules.pullbackComp (boundaryBaseFullMarkedIso q p π j hq z s hs O d).hom
      (coprod.desc (boundaryBaseWholeMap π d O) (boundaryBaseWholeMap π (s ≫ j) O))).symm.app M ≪≫
    (Modules.pullback (boundaryBaseFullMarkedIso q p π j hq z s hs O d).hom).mapIso e ≪≫
    Modules.pullbackUnitIso (boundaryBaseFullMarkedIso q p π j hq z s hs O d).hom

end AlgebraicGeometry.Scheme.Hom
