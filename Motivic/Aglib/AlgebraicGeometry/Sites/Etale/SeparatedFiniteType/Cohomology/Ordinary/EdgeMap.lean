/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Injectives
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageExact
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.RestrictionSource
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionEdgeMap

/-! # The actual ordinary cohomology edge map of geometric base change -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {S T : Scheme.{u}} (b : T ⟶ S)

/-- The genuine inverse image carries the original free source to the pulled-back free source. -/
def inverseImageSourceIso (V : EtaleSeparatedFiniteType S) :
    (inverseImage b).obj (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (nisnevichTopology S) V) ≅
      Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (nisnevichTopology T) ((baseChange b).obj V) :=
  Hypercohomology.restrictionSourceIso.{u + 1, u, u + 1, u + 1}
    (nisnevichTopology S) (nisnevichTopology T) (baseChange b) V

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

/-- Apply the actual exact inverse image, then the actual counit, with original free sources. -/
def ordinaryEdgeMap (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (n : ℕ) :
    LargeCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology S)
        ((directImage b).obj F) n V →+
      LargeCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology T)
        F n ((baseChange b).obj V) where
  toFun x := (Ext.mk₀ (inverseImageSourceIso b V).inv).comp
    ((imageAdjunction b).extEdge n x) (zero_add n)
  map_zero' := by simp
  map_add' x y := by simp

/-- The ordinary edge in degree zero is an isomorphism, without higher acyclicity inputs. -/
theorem ordinaryEdgeMap_zero_bijective (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    Function.Bijective (ordinaryEdgeMap b V F 0) := by
  let e := (((extFunctor 0).mapIso (inverseImageSourceIso b V).symm.op).app F)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  exact he.comp ((imageAdjunction b).extEdge_zero_bijective _ F)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
