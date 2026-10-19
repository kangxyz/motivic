module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.CurveGeometry
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.Boundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Common.GraphIdeal
/-! # The original diagonal ideal on the actual retained common target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S C Y B V : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (α : B ⟶ Y) (v : V ⟶ C) [IsOpenImmersion v]
  (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)

/-- The diagonal of the refined overlap in source times the original overlap. -/
def relativeRetainedGraph : B ⟶
    retainedProduct (commonProjection π j α) π v :=
  pullback.lift (𝟙 B) φ (by
    simpa only [Category.id_comp, commonProjection, Category.assoc] using
      congrArg (fun f => f ≫ π) hφ.symm)

omit [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  [IsOpenImmersion v] in
@[reassoc (attr := simp)] theorem relativeRetainedGraph_fst :
    relativeRetainedGraph π j α v φ hφ ≫ pullback.fst _ _ = 𝟙 B :=
  pullback.lift_fst _ _ _
omit [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  [IsOpenImmersion v] in
@[reassoc (attr := simp)] theorem relativeRetainedGraph_snd :
    relativeRetainedGraph π j α v φ hφ ≫ pullback.snd _ _ = φ :=
  pullback.lift_snd _ _ _

omit [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  [IsOpenImmersion v] in
/-- This is the literal original graph after the retained open inclusion. -/
theorem relativeRetainedGraph_inclusion :
    relativeRetainedGraph π j α v φ hφ ≫
      retainedProductInclusion (commonProjection π j α) π v =
    constantSourceGraph α π j := by
  apply pullback.hom_ext <;>
    simp [constantSourceGraph, relativeRetainedGraph, Category.assoc, hφ]

omit [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)] in
/-- The original lambda diagonal square stays Cartesian on the actual retained common curve. -/
theorem relativeRetainedGraph_isPullback :
    IsPullback α (relativeRetainedGraph π j α v φ hφ)
      (Hom.compactificationGraph π j)
      (retainedProductInclusion (commonProjection π j α) π v ≫
        commonToLambda π j α) := by
  have H : IsPullback (𝟙 B) (relativeRetainedGraph π j α v φ hφ)
      (constantSourceGraph α π j)
      (retainedProductInclusion (commonProjection π j α) π v) :=
    IsPullback.of_horiz_isIso_mono ⟨by
      simpa only [Category.id_comp] using (relativeRetainedGraph_inclusion π j α v φ hφ).symm⟩
  simpa only [Category.id_comp, commonToLambda, constantSourceMapOfEq, constantSourceMap] using
    H.paste_horiz (constantSourceGraph_isPullback α π j)

/-- The actual retained diagonal ideal is the pullback of the original lambda graph ideal. -/
def relativeRetainedGraphIdealIso [Flat α] :
    (Modules.pullback (retainedProductInclusion (commonProjection π j α) π v ≫
      commonToLambda π j α)).obj (Hom.relativeCompactificationGraphLine π j).val ≅
    Hom.idealModule (relativeRetainedGraph π j α v φ hφ) := by
  let J := Hom.compactificationGraph π j
  let w := retainedProductInclusion (commonProjection π j α) π v ≫
    commonToLambda π j α
  have : Flat (commonToLambda π j α) :=
    MorphismProperty.of_isPullback (commonToLambda_isPullback π j α).flip inferInstance
  have : Flat w := inferInstance
  have : (Hom.idealModule J).IsQuasicoherent := by
    have := Invertible.finiteLocallyFree_of_isLocallyRankOne
      (Hom.relativeCompactificationGraphLine π j).val
      (Hom.relativeCompactificationGraphLine π j).property
    exact inferInstanceAs ((Hom.relativeCompactificationGraphLine π j).val.IsQuasicoherent)
  have : IsClosedImmersion J := by dsimp [J, Hom.compactificationGraph]; infer_instance
  have H := relativeRetainedGraph_isPullback π j α v φ hφ
  have : IsClosedImmersion (relativeRetainedGraph π j α v φ hφ) :=
    MorphismProperty.of_isPullback H inferInstance
  let e := Hom.idealPullbackMap J (relativeRetainedGraph π j α v φ hφ) w α H.w
  have : IsIso e := Hom.idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact asIso e

/-- The comparison retains the original canonical functional, not only its zero support. -/
theorem relativeRetainedGraphIdealIso_inclusion [Flat α] :
    (relativeRetainedGraphIdealIso π j α v φ hφ).hom ≫
      Hom.idealInclusion (relativeRetainedGraph π j α v φ hφ) =
    Modules.Hom.pullbackToUnit
      (Hom.idealInclusion (Hom.compactificationGraph π j))
      (retainedProductInclusion (commonProjection π j α) π v ≫
        commonToLambda π j α) :=
  Hom.idealPullbackMap_inclusion _ _ _ _ _
end AlgebraicGeometry.Scheme.RelativeCurvePencil
