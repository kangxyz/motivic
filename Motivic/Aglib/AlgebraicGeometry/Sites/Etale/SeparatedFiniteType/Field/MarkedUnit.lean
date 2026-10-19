/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Unit

/-! # Unit representatives at literal marked neighborhoods -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

/-- Every literal marked point has the actual unit formula, not only the displayed
image of a point-category object. The restriction is its unique actual pullback lift. -/
@[reassoc]
theorem fieldNeighborhoodInverseImageIso_marked_ι
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T)
    (a : Over.mk (q ≫ b) ⟶ (MorphismProperty.Over.forget _ _ T).obj V) :
    colimit.ι ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ T ⋙
        coyoneda.obj (op (Over.mk (q ≫ b))))).op ⋙ G.obj)
      (op (Functor.elementsMk _ V a)) ≫
        (fieldNeighborhoodInverseImageIso b K q G).hom =
    ((imageAdjunction b).unit.app G).hom.app (op V) ≫
      ((inverseImage b).obj G).obj.map ((fieldPointLiftEquiv b K q V).symm a).op := by
  have h := fieldNeighborhoodInverseImageIso_ι b K q G V
    ((fieldPointLiftEquiv b K q V).symm a)
  have he : relativeFieldPointFiberEquiv b K q V
      (shrinkYonedaObjObjEquiv.{u + 1}.symm ((fieldPointLiftEquiv b K q V).symm a)) = a :=
    (relativeFieldPointFiberEquiv b K q V).apply_symm_apply a
  dsimp only [pointElementsToNeighborhood] at h
  rw [he] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
