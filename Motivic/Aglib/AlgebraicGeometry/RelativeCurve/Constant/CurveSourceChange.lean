/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.RetainedTarget

/-! # Actual source changes of constant retained curves -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {X S B K : Scheme.{u}} (α : X ⟶ S) (q : S ⟶ K) (π : B ⟶ K)

/-- The canonical map keeps the original target B unchanged. -/
def constantSourceMap : pullback (α ≫ q) π ⟶ pullback q π :=
  (IsPullback.of_hasPullback q π).flip.lift (pullback.snd _ _)
    (pullback.fst _ _ ≫ α) (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem constantSourceMap_fst : constantSourceMap α q π ≫ pullback.fst q π =
    pullback.fst (α ≫ q) π ≫ α :=
  (IsPullback.of_hasPullback q π).flip.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem constantSourceMap_snd : constantSourceMap α q π ≫ pullback.snd q π =
    pullback.snd (α ≫ q) π :=
  (IsPullback.of_hasPullback q π).flip.lift_fst _ _ _

/-- The source-square is Cartesian as a square of whole schemes. -/
theorem constantSourceMap_isPullback :
    IsPullback (constantSourceMap α q π) (pullback.fst (α ≫ q) π) (pullback.fst q π) α :=
  (IsPullback.of_hasPullback (α ≫ q) π).flip.of_right'
    (IsPullback.of_hasPullback q π).flip

/-- The graph in the source-changed constant curve, retaining the original target. -/
def constantSourceGraph (r : S ⟶ B) : X ⟶ pullback (α ≫ (r ≫ π)) π :=
  pullback.lift (𝟙 X) (α ≫ r) (by simp)

/-- The original graph square is Cartesian before passing to ideals or cycles. -/
theorem constantSourceGraph_isPullback (r : S ⟶ B) :
    IsPullback α (constantSourceGraph α π r) (Hom.compactificationGraph π r)
      (constantSourceMap α (r ≫ π) π) where
  w := by
    apply pullback.hom_ext <;>
      simp [constantSourceGraph, Hom.compactificationGraph, Category.assoc]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t => by
    refine ⟨t.snd ≫ pullback.fst _ _, ?_, ?_, ?_⟩
    · change (t.snd ≫ pullback.fst (α ≫ (r ≫ π)) π) ≫ α = t.fst
      have h := congrArg (fun m => m ≫ pullback.fst (r ≫ π) π) t.condition
      simpa only [Category.assoc, Hom.compactificationGraph, pullback.lift_fst,
        Category.comp_id, constantSourceMap_fst] using h.symm
    · change (t.snd ≫ pullback.fst (α ≫ (r ≫ π)) π) ≫
        constantSourceGraph α π r = t.snd
      apply pullback.hom_ext
      · simp [constantSourceGraph, Category.assoc]
      · have h := congrArg (fun m => m ≫ pullback.snd (r ≫ π) π) t.condition
        have hfst := congrArg (fun m => m ≫ pullback.fst (r ≫ π) π) t.condition
        simp only [Category.assoc, Hom.compactificationGraph, pullback.lift_fst,
          Category.comp_id, constantSourceMap_fst] at hfst
        simp only [Category.assoc, Hom.compactificationGraph, pullback.lift_snd,
          constantSourceMap_snd] at h
        simp only [Category.assoc, constantSourceGraph, pullback.lift_snd]
        exact (congrArg (fun v => v ≫ r) hfst.symm).trans h
    · intro m _ hm
      have h := congrArg (fun v => v ≫ pullback.fst (α ≫ (r ≫ π)) π) hm
      simpa [constantSourceGraph, Category.assoc] using h)⟩

/-- The original ideal, not merely its divisor class, is preserved under flat source change. -/
def constantSourceGraphIdealIso [Flat α] (r : S ⟶ B)
    [IsClosedImmersion (Hom.compactificationGraph π r)]
    [(Hom.idealModule (Hom.compactificationGraph π r)).IsQuasicoherent] :
    (Modules.pullback (constantSourceMap α (r ≫ π) π)).obj
      (Hom.idealModule (Hom.compactificationGraph π r)) ≅
      Hom.idealModule (constantSourceGraph α π r) := by
  have : Flat (constantSourceMap α (r ≫ π) π) :=
    MorphismProperty.of_isPullback (constantSourceMap_isPullback α (r ≫ π) π).flip inferInstance
  have : IsClosedImmersion (constantSourceGraph α π r) :=
    MorphismProperty.of_isPullback (constantSourceGraph_isPullback α π r) inferInstance
  let H := constantSourceGraph_isPullback α π r
  let v := Hom.idealPullbackMap (Hom.compactificationGraph π r)
    (constantSourceGraph α π r) (constantSourceMap α (r ≫ π) π) α H.w
  have : IsIso v := Hom.idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact asIso v

/-- The ideal comparison identifies the literal pulled canonical section. -/
theorem constantSourceGraphIdealIso_hom_inclusion [Flat α] (r : S ⟶ B)
    [IsClosedImmersion (Hom.compactificationGraph π r)]
    [(Hom.idealModule (Hom.compactificationGraph π r)).IsQuasicoherent] :
    (constantSourceGraphIdealIso α π r).hom ≫ Hom.idealInclusion (constantSourceGraph α π r) =
      Modules.Hom.pullbackToUnit (Hom.idealInclusion (Hom.compactificationGraph π r))
        (constantSourceMap α (r ≫ π) π) :=
  Hom.idealPullbackMap_inclusion _ _ _ _ _

/-- The same actual source map when the common source structure map is fixed in advance. -/
def constantSourceMapOfEq (qX : X ⟶ K) (h : qX = α ≫ q) :
    pullback qX π ⟶ pullback q π :=
  (IsPullback.of_hasPullback q π).flip.lift (pullback.snd _ _)
    (pullback.fst _ _ ≫ α) (by rw [Category.assoc, ← h, pullback.condition])

@[reassoc (attr := simp)]
theorem constantSourceMapOfEq_fst (qX : X ⟶ K) (h : qX = α ≫ q) :
    constantSourceMapOfEq α q π qX h ≫ pullback.fst q π = pullback.fst qX π ≫ α :=
  (IsPullback.of_hasPullback q π).flip.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem constantSourceMapOfEq_snd (qX : X ⟶ K) (h : qX = α ≫ q) :
    constantSourceMapOfEq α q π qX h ≫ pullback.snd q π = pullback.snd qX π :=
  (IsPullback.of_hasPullback q π).flip.lift_fst _ _ _

theorem constantSourceMapOfEq_isPullback (qX : X ⟶ K) (h : qX = α ≫ q) :
    IsPullback (constantSourceMapOfEq α q π qX h) (pullback.fst qX π) (pullback.fst q π) α := by
  subst qX
  exact constantSourceMap_isPullback α q π
end AlgebraicGeometry.Scheme
