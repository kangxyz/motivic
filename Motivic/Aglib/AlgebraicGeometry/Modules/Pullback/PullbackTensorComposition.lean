module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.PushforwardTensorComposition
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
/-! # Composition of the original tensor pullback comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual adjunction unit retains both native composition comparisons. -/
theorem pullbackTensorComposition_unit (M : Z.Modules) :
    (pullbackPushforwardAdjunction g).unit.app M ≫
      (pushforward g).map ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)) ≫
      (pushforward g).map ((pushforward f).map ((pullbackComp f g).hom.app M)) ≫
      (pushforwardComp f g).hom.app ((pullback (f ≫ g)).obj M) =
    (pullbackPushforwardAdjunction (f ≫ g)).unit.app M := by
  have h := homEquiv_conjugate
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv
    ((pullbackComp f g).hom.app M)
  rw [Iso.inv_hom_id_app, conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv] at h
  simp only [Adjunction.homEquiv_unit] at h
  exact h.symm
/-- Both tensor pullback stages agree with the original composite pullback comparison. -/
theorem pullbackTensorMap_comp (M N : Z.Modules) :
    (pullback f).map (pullbackTensorMap g M N) ≫
      pullbackTensorMap f ((pullback g).obj M) ((pullback g).obj N) ≫
      tensorSheafMap X ((pullbackComp f g).hom.app M) ((pullbackComp f g).hom.app N) =
    (pullbackComp f g).hom.app (tensorSheaf Z M N) ≫
      pullbackTensorMap (f ≫ g) M N := by
  apply (cancel_epi ((pullbackComp f g).inv.app (tensorSheaf Z M N))).mp
  rw [← Category.assoc _ ((pullbackComp f g).hom.app _), Iso.inv_hom_id_app, Category.id_comp]
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_conjugate, conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv]
  change (pullbackPushforwardAdjunction g).homEquiv _ _
    ((pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullback f).map (pullbackTensorMap g M N) ≫
        pullbackTensorMap f ((pullback g).obj M) ((pullback g).obj N) ≫
        tensorSheafMap X ((pullbackComp f g).hom.app M) ((pullbackComp f g).hom.app N))) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackTensorMap_adjoint, Adjunction.homEquiv_naturality_right,
    pullbackTensorMap_adjoint, pullbackTensorMap_adjoint]
  simp only [Category.assoc]
  rw [← pushforwardTensorMap_naturality]
  rw [← Category.assoc (tensorSheafMap Y _ _), tensorSheafMap_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← pushforwardTensorMap_naturality_assoc]
  rw [← Category.assoc (tensorSheafMap Z _ _), tensorSheafMap_comp]
  rw [pushforwardTensorMap_comp]
  rw [← Category.assoc, tensorSheafMap_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [pullbackTensorComposition_unit, pullbackTensorComposition_unit]
end AlgebraicGeometry.Scheme.Modules
