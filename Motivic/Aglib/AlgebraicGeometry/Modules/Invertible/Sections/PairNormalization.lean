module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.TensorSections
/-! # Normalize the actual Serre section pair through the native unit comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

def rightNormalizeSection {X : Scheme.{u}} (T : X.Modules)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T
      (SheafOfModules.unit X.ringCatSheaf)) : SheafOfModules.unit X.ringCatSheaf ⟶ T :=
  b ≫ (tensorSheafRightUnit X T).hom

/-- The normalized denominator retains its actual pulled boundary coefficient. -/
theorem pullbackSectionMap_rightNormalize {X W : Scheme.{u}} (f : W ⟶ X) (T : X.Modules)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T
      (SheafOfModules.unit X.ringCatSheaf)) :
    pullbackSectionMap f (rightNormalizeSection T b) =
      pullbackSectionMap f b ≫ pullbackTensorMap f T (SheafOfModules.unit X.ringCatSheaf) ≫
        tensorSheafMap W (𝟙 _) (pullbackUnitIso f).hom ≫
          (tensorSheafRightUnit W ((Modules.pullback f).obj T)).hom := by
  simp only [rightNormalizeSection, pullbackSectionMap, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [← pullbackTensorMap_rightUnit f T]

/-- The literal prescribed numerator equation becomes tensoring with the inverse boundary frame. -/
theorem prescribedPair_normalized {X W : Scheme.{u}} (f : W ⟶ X) (T M : X.Modules)
    (E : (Modules.pullback f).obj M ≅ SheafOfModules.unit W.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T M)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T
      (SheafOfModules.unit X.ringCatSheaf))
    (u : SheafOfModules.unit W.ringCatSheaf ⟶ tensorSheaf W
      ((Modules.pullback f).obj T) ((Modules.pullback f).obj
        (SheafOfModules.unit X.ringCatSheaf)))
    (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T M =
      u ≫ tensorSheafMap W (𝟙 _) ((pullbackUnitIso f).hom ≫ E.inv))
    (hb : pullbackSectionMap f b ≫ pullbackTensorMap f T
      (SheafOfModules.unit X.ringCatSheaf) = u) :
    pullbackSectionMap f a ≫ pullbackTensorMap f T M =
      tensorUnitSection (pullbackSectionMap f (rightNormalizeSection T b)) E.inv := by
  rw [pullbackSectionMap_rightNormalize, ← Category.assoc, hb]
  exact ha.trans (tensorUnitSection_normalized u (pullbackUnitIso f) E.inv).symm
end AlgebraicGeometry.Scheme.Modules.Invertible
