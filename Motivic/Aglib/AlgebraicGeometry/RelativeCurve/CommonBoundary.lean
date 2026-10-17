module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FullBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantBoundarySourceChange
/-! # Original source-change diagrams for a relative-curve correcting pencil -/
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

abbrev commonProjection := α ≫ (j ≫ π)
abbrev commonAmbient := pullback (commonProjection π j α) π
abbrev commonInfinity := pullback (pullback.snd (commonProjection π j α) π) d
abbrev commonZero := pullback (commonProjection π j α) (s ≫ j ≫ π)
abbrev commonBoundary := commonInfinity π j α d ⨿ commonZero π j α s

include hq h in
lemma commonProjection_fixed : commonProjection π j α = β ≫ (a ≫ q) := by
  dsimp only [commonProjection]
  rw [hq, ← Category.assoc, h, Category.assoc]

abbrev commonToLambda : commonAmbient π j α ⟶ pullback (j ≫ π) π :=
  constantSourceMapOfEq α (j ≫ π) π (commonProjection π j α) rfl
abbrev commonToPsi : commonAmbient π j α ⟶ pullback (a ≫ q) π :=
  constantSourceMapOfEq β (a ≫ q) π (commonProjection π j α)
    (commonProjection_fixed q π j p hq a α β h)

def commonZeroInclusion : commonZero π j α s ⟶ commonAmbient π j α :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s ≫ j)
    (by simpa only [Category.assoc] using (pullback.condition
      (f := commonProjection π j α) (g := s ≫ j ≫ π)))
abbrev commonBoundaryInclusion : commonBoundary π j α s d ⟶ commonAmbient π j α :=
  coprod.desc (pullback.fst _ _) (commonZeroInclusion π j α s)

def commonZeroToLambda : commonZero π j α s ⟶ pullback (j ≫ π) (s ≫ j ≫ π) :=
  constantSourceMapOfEq α (j ≫ π) (s ≫ j ≫ π) (commonProjection π j α) rfl

def commonZeroToPsi : commonZero π j α s ⟶ pullback (a ≫ q) (z ≫ q) :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _) (by
    have hz : s ≫ j ≫ π = z ≫ q := by rw [hq, ← Category.assoc, hs]
    rw [Category.assoc, ← commonProjection_fixed q π j p hq a α β h, pullback.condition]
    exact congrArg (fun f => pullback.snd (commonProjection π j α) (s ≫ j ≫ π) ≫ f) hz)

def commonBoundaryToLambda : commonBoundary π j α s d ⟶
    (pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)) :=
  coprod.map (constantInfinitySourceMap α (j ≫ π) π (commonProjection π j α) rfl d)
    (commonZeroToLambda π j α s)

def commonBoundaryToPsi : commonBoundary π j α s d ⟶
    (pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) :=
  coprod.map (constantInfinitySourceMap β (a ≫ q) π (commonProjection π j α)
    (commonProjection_fixed q π j p hq a α β h) d)
    (commonZeroToPsi q π j p hq a α β h z s hs)

lemma commonBoundaryToLambda_inclusion :
    commonBoundaryToLambda π j α s d ≫
      coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s) =
    commonBoundaryInclusion π j α s d ≫ commonToLambda π j α := by
  apply coprod.hom_ext
  · simp [commonBoundaryToLambda, Hom.infinityProductMap, commonBoundaryInclusion,
      commonToLambda]
  · simp only [commonBoundaryToLambda, coprod.inr_map_assoc, coprod.inr_desc,
      commonBoundaryInclusion, coprod.inr_desc_assoc]
    apply pullback.hom_ext <;> simp [commonZeroToLambda, Hom.graphBoundaryRestriction,
      commonZeroInclusion, commonToLambda, Category.assoc]

lemma commonToLambda_isPullback :
    IsPullback (commonToLambda π j α) (pullback.fst (commonProjection π j α) π)
      (pullback.fst (j ≫ π) π) α := constantSourceMapOfEq_isPullback α _ _ _ rfl
lemma commonToPsi_isPullback :
    IsPullback (commonToPsi q π j p hq a α β h) (pullback.fst (commonProjection π j α) π)
      (pullback.fst (a ≫ q) π) β :=
  constantSourceMapOfEq_isPullback β _ _ _ (commonProjection_fixed q π j p hq a α β h)

/-- The two source legs give the identical original target-curve coordinate map. -/
lemma commonZero_coordinate_eq :
    commonZeroToLambda π j α s ≫
      (Hom.relativeBoundaryProductIso q π j p hq z s hs).hom ≫
        Hom.boundaryProductMap q p z =
    commonZeroToPsi q π j p hq a α β h z s hs ≫ Hom.boundaryProductMap q a z := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Hom.boundaryProductMap, pullback.lift_fst,
      Hom.relativeBoundaryProductIso, pullback.congrHom]
    simp [commonZeroToLambda, commonZeroToPsi, Category.assoc, ← h]
  · simp [commonZeroToLambda, commonZeroToPsi, Hom.relativeBoundaryProductIso,
      Hom.boundaryProductMap, pullback.congrHom, Category.assoc]
end AlgebraicGeometry.Scheme.RelativeCurvePencil
