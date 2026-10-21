/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.Product.Ideals
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-! # Actual product sections commute with canonical tensor pullback -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PullbackTensor.Local

universe u
namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- The original tensor-to-unit coefficient map uses the canonical tensor map and unitor. -/
theorem tensorToUnit_eq_tensorSheafMap {X : Scheme.{u}} {L : X.Modules}
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) :
    (tensorToUnit a).app M =
      tensorSheafMap X a (𝟙 M) ≫ (tensorSheafLeftUnit X M).hom := rfl

/-- The actual pulled product equals the product of actual pulled factors,
through the canonical tensor comparison. No zero-scheme or cycle replacement is used. -/
theorem pullbackToUnit_productSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L M : Y.Modules} (a : L ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    pullbackToUnit (productSection a b) f =
      pullbackTensorMap f L M ≫ productSection (pullbackToUnit a f) (pullbackToUnit b f) := by
  simp only [pullbackToUnit, productSection, tensorToUnit_eq_tensorSheafMap,
    Functor.map_comp, Category.assoc]
  rw [← pullbackTensorMap_leftUnit f M]
  simp only [Category.assoc]
  rw [pullbackTensorMap_naturality_assoc]
  rw [tensorSheafMap_comp_assoc]
  simp only [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]

/-- For line bundles the comparison is exactly the canonical line-bundle tensor isomorphism. -/
theorem pullbackToUnit_productSection_lineBundle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L M : LineBundle Y) (a : L.val ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    pullbackToUnit (productSection a b) f =
      (pullbackLineBundleTensorIso f L M).hom ≫
        productSection (pullbackToUnit a f) (pullbackToUnit b f) :=
  pullbackToUnit_productSection f a b

end AlgebraicGeometry.Scheme.Modules.Hom
