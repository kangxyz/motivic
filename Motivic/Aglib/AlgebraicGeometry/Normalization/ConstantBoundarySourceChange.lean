module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantCurveSourceChange
/-! # Literal source change of both components of a constant curve boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {X S C K D Z : Scheme.{u}}
  (α : X ⟶ S) (q : S ⟶ K) (π : C ⟶ K) (qX : X ⟶ K) (h : qX = α ≫ q)
  (d : D ⟶ C) (z : Z ⟶ C)

/-- The infinity component changes only its source, retaining the whole boundary scheme. -/
def constantInfinitySourceMap :
    pullback (pullback.snd qX π) d ⟶ pullback (pullback.snd q π) d :=
  pullback.lift (pullback.fst _ _ ≫ constantSourceMapOfEq α q π qX h)
    (pullback.snd _ _) (by
      simp only [Category.assoc, constantSourceMapOfEq_snd]
      exact pullback.condition)

@[reassoc (attr := simp)] theorem constantInfinitySourceMap_fst :
    constantInfinitySourceMap α q π qX h d ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ constantSourceMapOfEq α q π qX h := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem constantInfinitySourceMap_snd :
    constantInfinitySourceMap α q π qX h d ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- The full Z-product inclusion, using the original Z and its original structure map. -/
def constantBoundaryZeroMap (q : S ⟶ K) : pullback q (z ≫ π) ⟶ pullback q π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z)
    (by simp only [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)] theorem constantBoundaryZeroMap_fst :
    constantBoundaryZeroMap π z q ≫ pullback.fst q π = pullback.fst _ _ :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem constantBoundaryZeroMap_snd :
    constantBoundaryZeroMap π z q ≫ pullback.snd q π = pullback.snd _ _ ≫ z :=
  pullback.lift_snd _ _ _

/-- Exact compatibility of the zero-boundary component with source change. -/
theorem constantBoundaryZeroMap_source :
    constantSourceMapOfEq α q (z ≫ π) qX h ≫ constantBoundaryZeroMap π z q =
      constantBoundaryZeroMap π z qX ≫ constantSourceMapOfEq α q π qX h := by
  apply pullback.hom_ext <;> simp only [Category.assoc, constantBoundaryZeroMap_fst,
    constantBoundaryZeroMap_snd, constantSourceMapOfEq_fst, constantSourceMapOfEq_snd,
    constantBoundaryZeroMap_fst_assoc, constantSourceMapOfEq_snd_assoc]

/-- The source change on the entire disjoint boundary, with neither component reduced. -/
def constantFullBoundarySourceMap :
    (pullback (pullback.snd qX π) d ⨿ pullback qX (z ≫ π)) ⟶
      (pullback (pullback.snd q π) d ⨿ pullback q (z ≫ π)) :=
  coprod.map (constantInfinitySourceMap α q π qX h d)
    (constantSourceMapOfEq α q (z ≫ π) qX h)

/-- The two original boundary inclusions commute with the actual ambient source change. -/
theorem constantFullBoundarySourceMap_inclusion :
    constantFullBoundarySourceMap α q π qX h d z ≫
      coprod.desc (pullback.fst _ _) (constantBoundaryZeroMap π z q) =
    coprod.desc (pullback.fst _ _) (constantBoundaryZeroMap π z qX) ≫
      constantSourceMapOfEq α q π qX h := by
  apply coprod.hom_ext
  · simp only [constantFullBoundarySourceMap, coprod.inl_map_assoc, coprod.inl_desc_assoc,
      coprod.inl_desc, constantInfinitySourceMap_fst]
  · simp only [constantFullBoundarySourceMap, coprod.inr_map_assoc,
      coprod.inr_desc_assoc, coprod.inr_desc]
    exact constantBoundaryZeroMap_source α q π qX h z
end AlgebraicGeometry.Scheme
