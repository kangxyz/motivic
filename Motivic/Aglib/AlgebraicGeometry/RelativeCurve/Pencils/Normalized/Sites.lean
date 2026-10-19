module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.CommonBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.RetainedSiteGeometry
/-! # Original source and overlap objects for the correcting correspondence -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]

theorem etaleLine_site_properties {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of (Polynomial k))) [Etale f] [QuasiCompact f] [IsSeparated f] :
    Smooth (f ≫ Hom.boundaryLineProjection k) ∧
      IsSeparated (f ≫ Hom.boundaryLineProjection k) ∧
      QuasiCompact (f ≫ Hom.boundaryLineProjection k) := by
  have := polynomialProjection_smooth_one k
  have : Smooth (Hom.boundaryLineProjection k) := SmoothOfRelativeDimension.smooth 1 _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable (r : S ⟶ Y) [IsOpenImmersion r] [QuasiCompact r]

/-- The actual refined lambda source, with its original field structure. -/
def diagonalSourceSite : SmoothSite (Spec (.of k)) := by
  have hh := etaleLine_site_properties k (r ≫ p)
  have he : ((r ≫ inclusion k p) ≫ projection k p) =
      (r ≫ p) ≫ Hom.boundaryLineProjection k := by
    simp only [Category.assoc, inclusion_projection]
  have : Smooth ((r ≫ inclusion k p) ≫ projection k p) := he ▸ hh.1
  have : IsSeparated ((r ≫ inclusion k p) ≫ projection k p) := he ▸ hh.2.1
  have : QuasiCompact ((r ≫ inclusion k p) ≫ projection k p) := he ▸ hh.2.2
  exact SmoothSite.mk ((r ≫ inclusion k p) ≫ projection k p)

/-- The unchanged fixed open source (in any actual affine presentation). -/
def fixedSourceSite (v : A ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion v] :
    SmoothSite (Spec (.of k)) := by
  have hh := etaleLine_site_properties k v
  have := hh.1
  have := hh.2.1
  have := hh.2.2
  exact SmoothSite.mk (v ≫ Hom.boundaryLineProjection k)

/-- The actual overlap is the target, never the base open alone. -/
def retainedTargetSite (U : (Spec (.of (Polynomial k))).Opens) :
    SmoothSite (Spec (.of k)) := by
  have hh := etaleLine_site_properties k (pullback.snd U.ι p ≫ p)
  have he : retainedProjection k p U =
      (pullback.snd U.ι p ≫ p) ≫ Hom.boundaryLineProjection k := by
    simp only [retainedProjection, retainedInclusion, Category.assoc, inclusion_projection]
  have : Smooth (retainedProjection k p U) := he ▸ hh.1
  have : IsSeparated (retainedProjection k p U) := he ▸ hh.2.1
  have : QuasiCompact (retainedProjection k p U) := he ▸ hh.2.2
  exact SmoothSite.mk (retainedProjection k p U)

/-- The common source is an actual open of the refined lambda source. -/
def commonSourceSite (α : X ⟶ S) [IsOpenImmersion α] [QuasiCompact α] :
    SmoothSite (Spec (.of k)) := by
  have hh := etaleLine_site_properties k (α ≫ r ≫ p)
  have he : commonSourceProjection k p r α =
      (α ≫ r ≫ p) ≫ Hom.boundaryLineProjection k := by
    simp only [commonSourceProjection, Category.assoc, inclusion_projection]
  have : Smooth (commonSourceProjection k p r α) := he ▸ hh.1
  have : IsSeparated (commonSourceProjection k p r α) := he ▸ hh.2.1
  have : QuasiCompact (commonSourceProjection k p r α) := he ▸ hh.2.2
  exact SmoothSite.mk (commonSourceProjection k p r α)

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
