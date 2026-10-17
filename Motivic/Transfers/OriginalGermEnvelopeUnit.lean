/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermFiberProduct

/-! # The original section embedding is the residue image-adjunction unit -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SmoothSite
open RelativeNisnevichNeighborhood
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
  (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
  (V : FiniteEtaleSite X.left) (x : X.left) (v : V.hom ⁻¹' {x})

/-- Identity reassociation of the original small neighborhood. -/
def originalFiberIdentityMap :
    smallObject (fiberProductToBase X V) v.1
      (compose (fiberProductToBase X V) v.1
        (NisnevichNeighborhood.identity ((FiniteEtaleSite.toSmoothSite X).obj V) v.1)) ⟶ V :=
  MorphismProperty.Over.homMk (𝟙 V.left) (by
    change 𝟙 V.left ≫ V.hom = (𝟙 V.left) ≫ V.hom
    rfl)

omit [IsAffine B] in
/-- The smooth restriction is literally the identity reassociation above. -/
theorem originalFiberIdentityMap_smooth :
    ((composeForgetIso (fiberProductToBase X V) v.1).app
      (NisnevichNeighborhood.identity ((FiniteEtaleSite.toSmoothSite X).obj V) v.1)).hom ≫
        (NisnevichNeighborhood.identity ((FiniteEtaleSite.toSmoothSite X).obj V) v.1).toBase =
      (FiniteEtaleSite.toSmoothSite X).map (originalFiberIdentityMap X V x v) := by
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

omit [IsAffine B] in
/-- The marked identity neighborhood lifts to the actual original fiber component. -/
theorem originalFiberIdentityLift :
    (FiniteEtaleSite.fieldPointLiftEquiv (X.left.fromSpecResidueField x)
      (V.left.residueField v.1) (V.hom.originalFiberFieldMap x v)
      (smallObject (fiberProductToBase X V) v.1
        (compose (fiberProductToBase X V) v.1
          (NisnevichNeighborhood.identity ((FiniteEtaleSite.toSmoothSite X).obj V) v.1)))).symm
      (originalSmallMark (fiberProductToBase X V) v.1 (X.left.fromSpecResidueField x)
        (V.hom.originalFiberFieldMap x v) (originalFiberFactorization X V x v)
        (NisnevichNeighborhood.identity ((FiniteEtaleSite.toSmoothSite X).obj V) v.1)) ≫
      (FiniteEtaleSite.baseChange (X.left.fromSpecResidueField x)).map
        (originalFiberIdentityMap X V x v) = FiniteEtaleSite.originalFiberObjectHom V x v := by
  apply (FiniteEtaleSite.fieldPointLiftEquiv (X.left.fromSpecResidueField x)
    (V.left.residueField v.1) (V.hom.originalFiberFieldMap x v) V).injective
  rw [FiniteEtaleSite.fieldPointLiftEquiv_naturality, Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  change V.left.fromSpecResidueField v.1 ≫ 𝟙 V.left =
    V.hom.originalFiberComponent x v ≫ V.hom.fiberι x
  rw [Category.comp_id, Scheme.Hom.originalFiberComponent_fiberι]
  rfl

/-- The original section-to-germ map becomes the literal image-adjunction unit. -/
@[reassoc]
theorem originalFiberGermIso_section :
    sectionToNisnevichPoint.{u, u + 1} F.obj ((FiniteEtaleSite.toSmoothSite X).obj V) v.1 ≫
      (originalFiberGermIso X F V x v).hom =
    ((FiniteEtaleSite.imageAdjunction (X.left.fromSpecResidueField x)).unit.app
      ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).hom.app (op V) ≫
        (originalResidueCoefficient X F x).obj.map
          (FiniteEtaleSite.originalFiberObjectHom V x v).op := by
  rw [sectionToNisnevichPoint, Category.assoc]
  change _ ≫ (_ ≫ (originalGermInverseImageOfFactorization F
    (fiberProductToBase X V) v.1 (X.left.fromSpecResidueField x)
      (V.hom.originalFiberFieldMap x v) (originalFiberFactorization X V x v)).hom) = _
  rw [originalGermInverseImageOfFactorization_ι, ← Category.assoc, ← F.obj.map_comp,
    ← op_comp, originalFiberIdentityMap_smooth]
  let d := originalFiberIdentityMap X V x v
  have hn := ((FiniteEtaleSite.imageAdjunction (X.left.fromSpecResidueField x)).unit.app
    ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).hom.naturality d.op
  change F.obj.map ((FiniteEtaleSite.toSmoothSite X).map d).op ≫ _ = _ at hn
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc]
  change _ ≫ ((originalResidueCoefficient X F x).obj.map
    ((FiniteEtaleSite.baseChange (X.left.fromSpecResidueField x)).map d).op ≫ _) = _
  congr 1
  erw [← (originalResidueCoefficient X F x).obj.map_comp]
  rw [← op_comp]
  exact congrArg (fun a ↦ (originalResidueCoefficient X F x).obj.map a.op)
    (originalFiberIdentityLift X V x v)

end Motivic.SmoothSite
