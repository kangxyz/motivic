/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Limits
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free

/-! # Native pullback comparisons on the two boundary components -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {D Z C : Scheme.{u}} (i : D ⟶ C) (j : Z ⟶ C)

/-- Restricting the actual boundary pullback to its first component is pullback along i. -/
def coprodPullbackRestrictLeft :
    pullback (coprod.desc i j) ⋙ restrictFunctor (coprod.inl : D ⟶ D ⨿ Z) ≅ pullback i :=
  Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback _) ≪≫
    pullbackComp _ _ ≪≫ pullbackCongr (coprod.inl_desc i j)

/-- Restricting the actual boundary pullback to Z retains the original full scheme Z. -/
def coprodPullbackRestrictRight :
    pullback (coprod.desc i j) ⋙ restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z) ≅ pullback j :=
  Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback _) ≪≫
    pullbackComp _ _ ≪≫ pullbackCongr (coprod.inr_desc i j)

end AlgebraicGeometry.Scheme.Modules
