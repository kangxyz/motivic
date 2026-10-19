module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionPullback
/-! Literal unit-normalized sections retain native tensor and composition comparisons. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :=
  pullbackSectionMap_comp f g s
example {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ N) :=
  pullbackSectionMap_tensorUnitSection f s t
#print axioms pullbackSectionMap_comp
#print axioms pullbackSectionMap_tensorUnitSection
