/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Enough injectives on the actual smooth Nisnevich site -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable (S : Scheme.{u})

/-- The original, possibly unequal-universe smooth-site category is Grothendieck abelian. -/
instance sheaf_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
by
  let : SmallCategory.{u + 1} (SmallModel.{u + 1} (SmoothSite S)) := inferInstance
  let J := (equivSmallModel.{u + 1} (SmoothSite S)).inverse.inducedTopology
    (nisnevichTopology S)
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    HasSheafify.mk' J AddCommGrpCat.{u + 1}
      (plusPlusAdjunction.{u + 1, u + 1, u + 2, u + 1, u + 1, u + 1}
        J AddCommGrpCat.{u + 1})
  let (X : (SmoothSite S)ᵒᵖ) : Limits.HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{u + 1} (SmoothSite S)).inverse.op)
      AddCommGrpCat.{u + 1} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (nisnevichTopology S) AddCommGrpCat.{u + 1}

/-- Ordinary smooth-site injective embeddings exist without any acyclicity premise. -/
theorem sheaf_enoughInjectives :
    EnoughInjectives (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) := inferInstance

end AlgebraicGeometry.Scheme.SmoothSite
