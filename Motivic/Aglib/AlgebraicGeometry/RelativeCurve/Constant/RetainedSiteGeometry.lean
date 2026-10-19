module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.RetainedTarget
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
/-! # The actual retained products are smooth-site curves -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (U : (Spec (.of (Polynomial k))).Opens) (q : S ⟶ Spec (.of k))

/-- Separation concerns the retained smooth curve, not a hypothetical smooth compactification. -/
theorem retainedProjection_separated : IsSeparated (retainedProjection k p U) := by
  change IsSeparated ((pullback.snd U.ι p ≫ inclusion k p) ≫ projection k p)
  rw [Category.assoc, inclusion_projection]
  infer_instance

omit [IsSeparated p] in
theorem retainedProjection_quasiCompact : QuasiCompact (retainedProjection k p U) := by
  change QuasiCompact ((pullback.snd U.ι p ≫ inclusion k p) ≫ projection k p)
  rw [Category.assoc, inclusion_projection]
  infer_instance

/-- All three site conditions are inherited on the original overlap product. -/
theorem constantRetainedTarget_site_properties
    [Smooth q] [IsSeparated q] [QuasiCompact q] :
    Smooth (pullback.fst q (retainedProjection k p U) ≫ q) ∧
      IsSeparated (pullback.fst q (retainedProjection k p U) ≫ q) ∧
      QuasiCompact (pullback.fst q (retainedProjection k p U) ≫ q) := by
  have := retainedProjection_separated k p U
  have := retainedProjection_quasiCompact k p U
  have := constantRetainedTarget_smooth k p U q
  have : Smooth (pullback.fst q (retainedProjection k p U)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsSeparated (pullback.fst q (retainedProjection k p U)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst q (retainedProjection k p U)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
