/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.FirstObstruction
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionExtFirstObstructionNaturality
public import Motivic.Aglib.CategoryTheory.Sites.RestrictionSourceNaturality
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.DegreeZero

/-! # Actual ordinary cohomology and the first right-direct-image obstruction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {S T : Scheme.{u}} (b : T ⟶ S)
  [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

omit [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})] in
/-- The constructed section obstruction commutes with the original restriction map. -/
theorem ordinaryFirstObstruction_naturality {V W : EtaleSeparatedFiniteType S} (a : V ⟶ W)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology T) F N ((baseChange b).obj W)) :
    ordinaryFirstObstruction b V F N
        ((LargeCohomology.presheaf (nisnevichTopology T) F N).map
          ((baseChange b).map a).op x) =
      (((directImage b).rightDerived N).obj F).obj.map a.op
        (ordinaryFirstObstruction b W F N x) := by
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
  rw [ordinaryFirstObstruction, ordinaryFirstObstruction,
    ← Hypercohomology.sectionsAddEquiv_naturality_left]
  congr 1
  rw [← (imageAdjunction b).extFirstObstruction_naturality]
  congr 1
  change (Ext.mk₀ (inverseImageSourceIso b V).hom).comp
    ((Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology T)).map
      ((baseChange b).map a))).comp x (zero_add N)) (zero_add N) =
    (Ext.mk₀ ((inverseImage b).map
      ((Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology S)).map a))).comp
        ((Ext.mk₀ (inverseImageSourceIso b W).hom).comp x (zero_add N)) (zero_add N)
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add N) (by omega), Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add N) (by omega), Ext.mk₀_comp_mk₀]
  congr 2
  exact (Hypercohomology.restrictionSourceIso_naturality
    (nisnevichTopology S) (nisnevichTopology T) (baseChange b) a).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
