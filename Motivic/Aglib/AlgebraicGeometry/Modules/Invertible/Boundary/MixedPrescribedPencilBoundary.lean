module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.MixedBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionPullback
/-! # The two prescribed boundary values give the actual signed-pencil boundary equality -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem tensorUnitSection_postcompose {W : Scheme.{u}}
    {M N P Q : W.Modules} (s : SheafOfModules.unit W.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit W.ringCatSheaf ⟶ N) (a : M ⟶ P) (b : N ⟶ Q) :
    tensorUnitSection s t ≫ tensorSheafMap W a b =
      tensorUnitSection (s ≫ a) (t ≫ b) := by
  simp only [tensorUnitSection, Category.assoc, tensorSheafMap_comp]

/-- The actual prescribed frame for lambda and coordinate-valued psi numerator imply
literal equality of the two tensor sections. The source maps and twists may differ. -/
theorem mixed_prescribed_boundary_tensor {X Y W : Scheme.{u}}
    (f : W ⟶ X) (g : W ⟶ Y) (I T : LineBundle X) (S : LineBundle Y)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d n : SheafOfModules.unit Y.ringCatSheaf ⟶ S.val)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (E : (Modules.pullback f).obj (dualLineBundle X I).val ≅
      SheafOfModules.unit W.ringCatSheaf)
    (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle X I).val =
      tensorUnitSection (pullbackSectionMap f b) E.inv)
    (hn : pullbackSectionMap g n =
      (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom) ≫
        pullbackSectionMap g d) :
    tensorSectionMap W (pullbackSectionMap f a) (pullbackSectionMap g n) =
      tensorSectionMap W (pullbackSectionMap f (twistedIdealSection X I T φ b))
        (pullbackSectionMap g d) := by
  let F := pullbackTensorMap f T.val (dualLineBundle X I).val
  have : IsIso F := PullbackTensor.Local.pullbackTensorMap_isIso f T.val
    (dualLineBundle X I).val T.property
  have : IsIso (tensorSheafMap W F (𝟙 ((Modules.pullback g).obj S.val))) := by
    change IsIso (tensorSheafIso W (asIso F) (Iso.refl _)).hom
    infer_instance
  apply (cancel_mono (tensorSheafMap W F (𝟙 ((Modules.pullback g).obj S.val)))).mp
  change tensorUnitSection _ _ ≫ _ = tensorUnitSection _ _ ≫ _
  rw [tensorUnitSection_postcompose, tensorUnitSection_postcompose]
  simp only [Category.comp_id]
  change tensorUnitSection (pullbackSectionMap f a ≫
      pullbackTensorMap f T.val (dualLineBundle X I).val) _ = _
  rw [ha, hn]
  have ht := pullbackSectionMap_tensorUnitSection f b (canonicalDualHom X I.val φ)
  change pullbackSectionMap f (twistedIdealSection X I T φ b) ≫
      pullbackTensorMap f T.val (dualLineBundle X I).val = _ at ht
  rw [ht]
  exact tensorUnitSection_prescribed_coordinate E
    (pullbackSectionMap f (canonicalDualHom X I.val φ))
    (pullbackSectionMap f b) (pullbackSectionMap g d)

/-- The two genuine prescribed section values give the literal pencil functional equality
through the original mixed-source line isomorphism. -/
theorem mixed_prescribed_boundary_functional {X Y W : Scheme.{u}}
    (f : W ⟶ X) (g : W ⟶ Y) (I T : LineBundle X) (S : LineBundle Y)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d n : SheafOfModules.unit Y.ringCatSheaf ⟶ S.val)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (E : (Modules.pullback f).obj (dualLineBundle X I).val ≅
      SheafOfModules.unit W.ringCatSheaf)
    (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle X I).val =
      tensorUnitSection (pullbackSectionMap f b) E.inv)
    (hn : pullbackSectionMap g n =
      (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom) ≫
        pullbackSectionMap g d) :
    (mixedPulledDualTwistedIdealProductIso f g I T S).hom ≫
      Hom.productSection
        (Hom.pullbackToUnit
          (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S n) g) =
    Hom.productSection (Hom.pullbackToUnit φ f)
      (Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X T b) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S d) g)) := by
  exact mixedPulledDualTwistedIdealProductIso_boundary f g I T S φ b d n a
    (mixed_prescribed_boundary_tensor f g I T S φ b d n a E ha hn)
end AlgebraicGeometry.Scheme.Modules.Invertible
