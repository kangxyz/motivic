module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.SectionPairNormalization
/-! # Native pullback of literal unit-domain tensor sections -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem pullback_rightUnit_inv {X W : Scheme.{u}} (f : W ⟶ X) (M : X.Modules) :
    (Modules.pullback f).map (tensorSheafRightUnit X M).inv ≫
      pullbackTensorMap f M (SheafOfModules.unit X.ringCatSheaf) ≫
        tensorSheafMap W (𝟙 _) (pullbackUnitIso f).hom =
      (tensorSheafRightUnit W ((Modules.pullback f).obj M)).inv := by
  apply (cancel_mono (tensorSheafRightUnit W ((Modules.pullback f).obj M)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [pullbackTensorMap_rightUnit f M]
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Pullback preserves the literal tensor of sections via the native tensor and unit maps. -/
theorem pullbackSectionMap_tensorUnitSection {X W : Scheme.{u}} (f : W ⟶ X)
    {M N : X.Modules} (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    pullbackSectionMap f (tensorUnitSection s t) ≫ pullbackTensorMap f M N =
      tensorUnitSection (pullbackSectionMap f s) (pullbackSectionMap f t) := by
  rw [tensorUnitSection_eq_rightUnit, tensorUnitSection_eq_rightUnit]
  simp only [pullbackSectionMap, CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := pullbackTensorMap_naturality f (𝟙 M) t
  rw [CategoryTheory.Functor.map_id] at hn
  rw [hn]
  rw [← pullback_rightUnit_inv f M]
  simp only [Category.assoc]
  rw [tensorSheafMap_comp]
  simp only [Category.id_comp, Iso.hom_inv_id_assoc]

/-- Normalized section pullback respects the original composition comparison. -/
theorem pullbackSectionMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    pullbackSectionMap f (pullbackSectionMap g s) ≫ (Modules.pullbackComp f g).hom.app M =
      pullbackSectionMap (f ≫ g) s := by
  have hu : (pullbackUnitIso f).inv ≫
      (Modules.pullback f).map (pullbackUnitIso g).inv ≫
      (Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) =
      (pullbackUnitIso (f ≫ g)).inv := by
    apply (cancel_mono (pullbackUnitIso (f ≫ g)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [pullbackUnitIso_comp]
    rw [← Category.assoc ((Modules.pullback f).map (pullbackUnitIso g).inv),
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id]
  simp only [pullbackSectionMap, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [(Modules.pullbackComp f g).hom.naturality s]
  simpa only [Category.assoc] using
    congrArg (fun h => h ≫ (Modules.pullback (f ≫ g)).map s) hu
end AlgebraicGeometry.Scheme.Modules.Invertible
