/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPoint
public import Motivic.Cohomology.A1.BoundaryCokernelSheaf
public import Mathlib.CategoryTheory.Sites.Point.Comap

/-! # Field evaluation of the genuine small-site inverse image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

instance baseChange_representablyFlat : RepresentablyFlat (baseChange b) :=
  flat_of_preservesFiniteLimits _

instance relativeFieldPoint_initiallySmall :
    InitiallySmall.{u + 1} (baseChange b ⋙ (fieldPoint K q).fiber).Elements :=
  initiallySmall_of_essentiallySmall _

/-- The actual point induced by field-valued points on base-changed étale neighborhoods. -/
def relativeFieldPoint : (nisnevichTopology T).Point.{u + 1} :=
  (fieldPoint K q).comap (baseChange b)
    (CoverPreserving.of_isContinuous (baseChange b) _ _)

/-- Evaluation of the original inverse image is the original comapped point fiber.
The inverse image is the genuine left adjoint, not naive restriction along `b`. -/
def relativeFieldPointInverseImageIso :
    (relativeFieldPoint b K q).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      inverseImage b ⋙ sheafToPresheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} ⋙
        (evaluation (FiniteEtaleSite S)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op (fieldObject K q)) :=
  (fieldPoint K q).sheafFiberComapIso (baseChange b)
      (CoverPreserving.of_isContinuous (baseChange b) _ _) AddCommGrpCat.{u + 1} ≪≫
    Functor.isoWhiskerLeft (inverseImage b) (fieldPointSheafFiberIso K q AddCommGrpCat.{u + 1})

end Motivic.FiniteEtaleSite
