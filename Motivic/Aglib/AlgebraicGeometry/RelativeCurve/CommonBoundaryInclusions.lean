module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CommonBoundary
/-! # Both original ambient boundary inclusions commute with source change -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)

def psiZeroInclusion : pullback (a ≫ q) (z ≫ q) ⟶ pullback (a ≫ q) π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s ≫ j) (by
    rw [Category.assoc, Category.assoc, hq, ← Category.assoc s, hs]
    exact pullback.condition)

abbrev psiBoundaryInclusion :
    (pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) ⟶ pullback (a ≫ q) π :=
  coprod.desc (pullback.fst _ _) (psiZeroInclusion q π j p hq a z s hs)

lemma commonBoundaryToPsi_inclusion :
    commonBoundaryToPsi q π j p hq a α β h z s hs d ≫
      psiBoundaryInclusion q π j p hq a z s hs d =
    commonBoundaryInclusion π j α s d ≫ commonToPsi q π j p hq a α β h := by
  apply coprod.hom_ext
  · simp [commonBoundaryToPsi, psiBoundaryInclusion, commonBoundaryInclusion, commonToPsi]
  · simp only [commonBoundaryToPsi, psiBoundaryInclusion, coprod.inr_map_assoc,
      coprod.inr_desc, commonBoundaryInclusion, coprod.inr_desc_assoc]
    apply pullback.hom_ext <;>
      simp [commonZeroToPsi, psiZeroInclusion, commonZeroInclusion, commonToPsi, Category.assoc]
end AlgebraicGeometry.Scheme.RelativeCurvePencil
