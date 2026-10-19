module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Product
/-! # Literal scalar transfer in the boundary product pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem unitEnd_apply (X : Scheme.{u})
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (x : Γ(X, U)) : c.val.app (op U) x =
      x * (show Γ(X, U) from c.val.app (op U) (1 : Γ(X, U))) := by
  have h := (c.val.app (op U)).hom.map_smul x (1 : Γ(X, U))
  simpa using h

/-- A structure-module scalar can be applied before a section or after its dual functional. -/
theorem sectionDualFunctional_unitEnd (X : Scheme.{u}) (L : LineBundle X)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    sectionDualFunctional X L (c ≫ s) = sectionDualFunctional X L s ≫ c := by
  ext U d
  rw [sectionDualFunctional_apply]
  change d.val.app (op (Over.mk (𝟙 U.unop))) (s.val.app U (c.val.app U (1 : X.presheaf.obj U))) =
    c.val.app U ((sectionDualFunctional X L s).val.app U d)
  rw [sectionDualFunctional_apply]
  have hs := (s.val.app U).hom.map_smul (c.val.app U (1 : X.presheaf.obj U)) (1 : X.presheaf.obj U)
  have hd := d.property (op (Over.mk (𝟙 U.unop)))
    (c.val.app U (1 : X.presheaf.obj U)) (s.val.app U (1 : X.presheaf.obj U))
  have hc := unitEnd_apply X c U.unop
    (d.val.app (op (Over.mk (𝟙 U.unop))) (s.val.app U (1 : X.presheaf.obj U)))
  have hs' : s.val.app U (c.val.app U (1 : X.presheaf.obj U)) =
      (c.val.app U (1 : X.presheaf.obj U)) • s.val.app U (1 : X.presheaf.obj U) := by
    simpa only [smul_eq_mul, mul_one] using hs
  apply (congrArg (fun x => d.val.app (op (Over.mk (𝟙 U.unop))) x) hs').trans
  apply hd.trans
  change (show X.presheaf.obj U from c.val.app U (1 : X.presheaf.obj U)) *
    (show X.presheaf.obj U from d.val.app (op (Over.mk (𝟙 U.unop)))
      (s.val.app U (1 : X.presheaf.obj U))) = _
  exact (mul_comm _ _).trans hc.symm

/-- Scalars transfer between the two original product factors, with no reduction of zeros. -/
theorem productSection_unitEnd {X : Scheme.{u}} {L M : X.Modules}
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Hom.productSection a (b ≫ c) = Hom.productSection a b ≫ c := by
  apply moduleTensor_hom_ext
  intro U l m
  erw [Hom.productSection_tensor]

/-- A scalar on the first factor is the same original scalar on the product. -/
theorem productSection_unitEnd_left {X : Scheme.{u}} {L M : X.Modules}
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Hom.productSection (a ≫ c) b = Hom.productSection a b ≫ c := by
  apply moduleTensor_hom_ext
  intro U l m
  have h1 := Hom.productSection_tensor (a ≫ c) b U l m
  have h2 := Hom.productSection_tensor a b U l m
  apply h1.trans
  change (show Γ(X, U) from c.val.app (op U) (a.app U l)) *
      (show Γ(X, U) from b.app U m) =
    c.val.app (op U) ((Hom.productSection a b).app U (moduleTensorSection X L M U l m))
  apply Eq.trans _ (congrArg (fun x => c.val.app (op U) x) h2).symm
  have hc := (c.val.app (op U)).hom.map_smul
    (show Γ(X, U) from b.app U m) (show Γ(X, U) from a.app U l)
  change c.val.app (op U) ((show Γ(X, U) from b.app U m) *
    (show Γ(X, U) from a.app U l)) = (show Γ(X, U) from b.app U m) *
    (show Γ(X, U) from c.val.app (op U) (a.app U l)) at hc
  exact (mul_comm (show Γ(X, U) from c.val.app (op U) (a.app U l))
    (show Γ(X, U) from b.app U m)).trans (hc.symm.trans
      (congrArg (fun x => c.val.app (op U) x)
        (mul_comm (show Γ(X, U) from b.app U m) (show Γ(X, U) from a.app U l))))

/-- The literal global line comparison transfers the prescribed coordinate ratio from ψ
onto the original diagonal functional. This is the boundary equation of the signed pencil. -/
theorem dualTwistedIdealProductIso_coordinate (X : Scheme.{u}) (I T S : LineBundle X)
    (ε : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶ S.val)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (dualTwistedIdealProductIso X I T S).hom ≫
      Hom.productSection
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T ε b))
        (sectionDualFunctional X S (c ≫ d)) =
      Hom.productSection (ε ≫ c)
        (Hom.productSection (sectionDualFunctional X T b) (sectionDualFunctional X S d)) := by
  rw [sectionDualFunctional_unitEnd, productSection_unitEnd,
    ← Category.assoc, dualTwistedIdealProductIso_section, productSection_unitEnd_left]
end AlgebraicGeometry.Scheme.Modules.Invertible
