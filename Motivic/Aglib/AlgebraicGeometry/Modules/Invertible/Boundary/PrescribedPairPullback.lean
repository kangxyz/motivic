module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.PullbackTensorComposition
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnOpen
/-! # The literal prescribed numerator value survives actual source change -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The original boundary frame, using the native composition comparison. -/
def compositeBoundaryFrame {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
    (M : X.Modules)
    (E : (Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Modules.pullback (f ≫ g)).obj M ≅ SheafOfModules.unit W.ringCatSheaf :=
  ((Modules.pullbackComp f g).app M).symm ≪≫
    (Modules.pullback f).mapIso E ≪≫ pullbackUnitIso f

/-- Pulling back the prescribed numerator equation retains its actual inverse frame,
not merely the existence of some trivialization. -/
theorem prescribed_pair_pullback {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
    (T M : X.Modules)
    (E : (Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T M)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (ha : pullbackSectionMap g a ≫ pullbackTensorMap g T M =
      tensorUnitSection (pullbackSectionMap g b) E.inv) :
    pullbackSectionMap (f ≫ g) a ≫ pullbackTensorMap (f ≫ g) T M =
      tensorUnitSection (pullbackSectionMap (f ≫ g) b)
        (compositeBoundaryFrame f g M E).inv := by
  have hh := congrArg (fun v => (pullbackUnitIso f).inv ≫
    (Modules.pullback f).map v) ha
  simp only [CategoryTheory.Functor.map_comp] at hh
  have hh' := congrArg (fun v => v ≫
    pullbackTensorMap f ((Modules.pullback g).obj T) ((Modules.pullback g).obj M) ≫
      tensorSheafMap W ((Modules.pullbackComp f g).hom.app T)
        ((Modules.pullbackComp f g).hom.app M)) hh
  change pullbackSectionMap f (pullbackSectionMap g a) ≫
      (Modules.pullback f).map (pullbackTensorMap g T M) ≫
      pullbackTensorMap f ((Modules.pullback g).obj T) ((Modules.pullback g).obj M) ≫
      tensorSheafMap W ((Modules.pullbackComp f g).hom.app T)
        ((Modules.pullbackComp f g).hom.app M) = _ at hh'
  rw [pullbackTensorMap_comp] at hh'
  rw [← Category.assoc, pullbackSectionMap_comp] at hh'
  rw [hh']
  change pullbackSectionMap f (tensorUnitSection (pullbackSectionMap g b) E.inv) ≫
    pullbackTensorMap f ((Modules.pullback g).obj T) ((Modules.pullback g).obj M) ≫ _ = _
  rw [← Category.assoc, pullbackSectionMap_tensorUnitSection]
  simp only [tensorUnitSection, Category.assoc, tensorSheafMap_comp]
  rw [pullbackSectionMap_comp]
  rfl

/-- The prescribed coordinate scalar of the original divisor frame is retained literally. -/
theorem compositeBoundaryFrame_coordinate {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
    (M : X.Modules)
    (E : (Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (δ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    pullbackSectionMap (f ≫ g) δ ≫ (compositeBoundaryFrame f g M E).hom =
      Scheme.Hom.unitEndomorphismPullback f (pullbackSectionMap g δ ≫ E.hom) := by
  rw [← pullbackSectionMap_comp f g δ]
  simp only [compositeBoundaryFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  simp only [pullbackSectionMap, Scheme.Hom.unitEndomorphismPullback,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hc : (Modules.pullbackComp f g).hom.app M ≫
      ((Modules.pullbackComp f g).app M).inv = 𝟙 _ :=
    ((Modules.pullbackComp f g).app M).hom_inv_id
  rw [← Category.assoc ((Modules.pullbackComp f g).hom.app M), hc, Category.id_comp]

/-- The original coordinate-valued psi numerator survives source change with the same scalar. -/
theorem scalar_pair_pullback {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
    {M : X.Modules} (n d : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (c : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (hn : pullbackSectionMap g n = c ≫ pullbackSectionMap g d) :
    pullbackSectionMap (f ≫ g) n = Scheme.Hom.unitEndomorphismPullback f c ≫
      pullbackSectionMap (f ≫ g) d := by
  rw [← pullbackSectionMap_comp f g n, ← pullbackSectionMap_comp f g d, hn]
  simp only [pullbackSectionMap, Scheme.Hom.unitEndomorphismPullback,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
end AlgebraicGeometry.Scheme.Modules.Invertible
