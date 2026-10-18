/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSourceComposition

/-! # Original free-source comparison on commuting geometric squares -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite

/-- Equality transport of the actual base morphism retains the canonical source map. -/
@[reassoc]
theorem inverseImageSourceIso_congr {R S : Scheme.{u}} {b c : R ⟶ S}
    (h : b = c) (V : FiniteEtaleSite S) :
    ((eqToIso (congrArg inverseImage h)).hom.app
        (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology S) V)) ≫
      (inverseImageSourceIso c V).hom =
    (inverseImageSourceIso b V).hom ≫
      (Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology R)).map
        ((eqToIso (congrArg baseChange h)).hom.app V) := by
  subst c
  simp

variable {Z' Z Y' Y : Scheme.{u}} (i : Z ⟶ Y) (i' : Z' ⟶ Y')
  (hZ : Z' ⟶ Z) (hY : Y' ⟶ Y) (w : hZ ≫ i = i' ≫ hY)

/-- The square comparison uses only the original inverse-image composition maps. -/
def inverseImageSquareIso : inverseImage i ⋙ inverseImage hZ ≅
    inverseImage hY ⋙ inverseImage i' :=
  inverseImageCompIso hZ i ≪≫ eqToIso (congrArg inverseImage w) ≪≫
    (inverseImageCompIso i' hY).symm

/-- The same square on actual etale neighborhoods, with native iterated pullbacks. -/
def baseChangeSquareIso : baseChange i ⋙ baseChange hZ ≅ baseChange hY ⋙ baseChange i' :=
  (MorphismProperty.Over.pullbackComp
    (P := etaleSeparatedFiniteType) (Q := ⊤) hZ i).symm ≪≫
      eqToIso (congrArg baseChange w) ≪≫
        MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤) i' hY

/-- The original free sources commute with the genuine inverse-image square,
not merely with a chosen objectwise isomorphism. -/
theorem inverseImageSourceIso_square (V : FiniteEtaleSite Y) :
    (inverseImage hZ).map (inverseImageSourceIso i V).hom ≫
      (inverseImageSourceIso hZ ((baseChange i).obj V)).hom ≫
        (Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology Z')).map
          ((baseChangeSquareIso i i' hZ hY w).hom.app V) =
    (inverseImageSquareIso i i' hZ hY w).hom.app
        (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology Y) V) ≫
      (inverseImage i').map (inverseImageSourceIso hY V).hom ≫
        (inverseImageSourceIso i' ((baseChange hY).obj V)).hom := by
  let A := Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1} (nisnevichTopology Z')
  let S := Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology Y) V
  let e₁ := MorphismProperty.Over.pullbackComp
    (P := etaleSeparatedFiniteType) (Q := ⊤) hZ i
  let e₂ := MorphismProperty.Over.pullbackComp
    (P := etaleSeparatedFiniteType) (Q := ⊤) i' hY
  let a₁ := (inverseImageCompIso hZ i).hom.app S
  have hright : (inverseImageSourceIso (i' ≫ hY) V).hom ≫ A.map (e₂.hom.app V) =
      (inverseImageCompIso i' hY).inv.app S ≫
        (inverseImage i').map (inverseImageSourceIso hY V).hom ≫
          (inverseImageSourceIso i' ((baseChange hY).obj V)).hom := by
    apply (cancel_mono (A.map (e₂.inv.app V))).mp
    simp only [Category.assoc, ← A.map_comp, e₂.hom_inv_id_app]
    rw [inverseImageSourceIso_comp]
    have hl : (inverseImageSourceIso (i' ≫ hY) V).hom ≫
        A.map (𝟙 ((baseChange (i' ≫ hY)).obj V)) =
        (inverseImageSourceIso (i' ≫ hY) V).hom :=
      (congrArg (fun z => (inverseImageSourceIso (i' ≫ hY) V).hom ≫ z)
        (A.map_id _)).trans (Category.comp_id _)
    have hr : (inverseImageCompIso i' hY).inv.app S ≫
        (inverseImageCompIso i' hY).hom.app S ≫
          (inverseImageSourceIso (i' ≫ hY) V).hom =
        (inverseImageSourceIso (i' ≫ hY) V).hom :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (inverseImageSourceIso (i' ≫ hY) V).hom)
          ((inverseImageCompIso i' hY).inv_hom_id_app S)).trans (Category.id_comp _))
    exact hl.trans hr.symm
  change _ = (a₁ ≫ (eqToIso (congrArg inverseImage w)).hom.app S ≫
      (inverseImageCompIso i' hY).inv.app S) ≫ _ ≫ _
  change (inverseImage hZ).map (inverseImageSourceIso i V).hom ≫
      (inverseImageSourceIso hZ ((baseChange i).obj V)).hom ≫
        A.map ((e₁.inv.app V ≫ (eqToIso (congrArg baseChange w)).hom.app V) ≫
          e₂.hom.app V) = _
  rw [A.map_comp, A.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ (A.map (e₁.inv.app V)),
    ← Category.assoc _ ((inverseImageSourceIso hZ ((baseChange i).obj V)).hom ≫
      A.map (e₁.inv.app V))]
  rw [inverseImageSourceIso_comp]
  simp only [Category.assoc]
  rw [← inverseImageSourceIso_congr_assoc w V]
  exact congrArg (fun z => a₁ ≫ (eqToIso (congrArg inverseImage w)).hom.app S ≫ z) hright

end Motivic.FiniteEtaleSite
