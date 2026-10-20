module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.Boundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.CurveGeometry
/-! # Actual source changes on the retained relative target curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B C V : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a) (v : V ⟶ C)

/-- The lambda source change on the retained target product. -/
abbrev retainedToLambda : retainedProduct (commonProjection π j α) π v ⟶
    retainedProduct (j ≫ π) π v :=
  constantSourceMapOfEq α (j ≫ π) (v ≫ π) (commonProjection π j α) rfl
/-- The psi source change on the retained target product. -/
abbrev retainedToPsi : retainedProduct (commonProjection π j α) π v ⟶
    retainedProduct (a ≫ q) π v :=
  constantSourceMapOfEq β (a ≫ q) (v ≫ π) (commonProjection π j α)
    (commonProjection_fixed q π j p hq a α β h)

lemma retainedToLambda_isPullback :
    IsPullback (retainedToLambda π j α v) (pullback.fst _ _)
      (pullback.fst (j ≫ π) (v ≫ π)) α :=
  constantSourceMapOfEq_isPullback α _ _ _ rfl
lemma retainedToPsi_isPullback :
    IsPullback (retainedToPsi q π j p hq a α β h v) (pullback.fst _ _)
      (pullback.fst (a ≫ q) (v ≫ π)) β :=
  constantSourceMapOfEq_isPullback β _ _ _ (commonProjection_fixed q π j p hq a α β h)

@[reassoc] lemma retainedToLambda_target :
    retainedToLambda π j α v ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [retainedToLambda]
@[reassoc] lemma retainedToPsi_target :
    retainedToPsi q π j p hq a α β h v ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [retainedToPsi]

lemma retainedToLambda_inclusion :
    retainedToLambda π j α v ≫ retainedProductInclusion (j ≫ π) π v =
    retainedProductInclusion (commonProjection π j α) π v ≫ commonToLambda π j α := by
  apply pullback.hom_ext <;>
    simp [retainedToLambda, commonToLambda, Category.assoc]
lemma retainedToPsi_inclusion :
    retainedToPsi q π j p hq a α β h v ≫ retainedProductInclusion (a ≫ q) π v =
    retainedProductInclusion (commonProjection π j α) π v ≫
      commonToPsi q π j p hq a α β h := by
  apply pullback.hom_ext <;>
    simp [retainedToPsi, commonToPsi, Category.assoc]
end AlgebraicGeometry.Scheme.RelativeCurvePencil
