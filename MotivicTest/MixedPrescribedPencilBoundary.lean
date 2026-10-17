module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.MixedPrescribedPencilBoundary
/-! Actual prescribed values imply the original mixed-source pencil functional equation. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
example {X Y W : Scheme.{u}}
    (f : W ⟶ X) (g : W ⟶ Y) (I T : LineBundle X) (S : LineBundle Y)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d n : SheafOfModules.unit Y.ringCatSheaf ⟶ S.val)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (E : (Scheme.Modules.pullback f).obj (dualLineBundle X I).val ≅
      SheafOfModules.unit W.ringCatSheaf)
    (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle X I).val =
      tensorUnitSection (X := W)
        (M := (Scheme.Modules.pullback f).obj T.val)
        (N := (Scheme.Modules.pullback f).obj (dualLineBundle X I).val)
        (pullbackSectionMap f b) E.inv)
    (hn : pullbackSectionMap g n =
      (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom) ≫
        pullbackSectionMap g d) :=
  mixed_prescribed_boundary_functional f g I T S φ b d n a E ha hn
#print axioms mixed_prescribed_boundary_functional
