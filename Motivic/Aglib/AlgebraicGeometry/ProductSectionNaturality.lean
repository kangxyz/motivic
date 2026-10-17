module
public import Motivic.Aglib.AlgebraicGeometry.ProductSectionIdeals
/-! # Actual product sections commute with domain maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- Domain changes act on both original section factors. -/
theorem productSection_naturality {X : Scheme.{u}} {L L' M M' : X.Modules}
    (f : L ⟶ L') (g : M ⟶ M')
    (a : L' ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M' ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap X f g ≫ productSection a b = productSection (f ≫ a) (g ≫ b) := by
  apply moduleTensor_hom_ext
  intro U l m
  change (productSection a b).app U
    ((tensorSheafMap X f g).val.app (Opposite.op U) (moduleTensorSection X L M U l m)) = _
  have hm := tensorSheafMap_tmul X f g (Opposite.op U) l m
  change (tensorSheafMap X f g).val.app (Opposite.op U) (moduleTensorSection X L M U l m) =
    moduleTensorSection X L' M' U (f.app U l) (g.app U m) at hm
  rw [hm]
  exact (productSection_tensor a b U (f.app U l) (g.app U m)).trans
    (productSection_tensor (f ≫ a) (g ≫ b) U l m).symm
end AlgebraicGeometry.Scheme.Modules.Hom
