module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.CommonBoundary
/-! # The original diagonal ideal on the actual retained common target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (α : X ⟶ S)
  (U : (Spec (.of (Polynomial k))).Opens) (φ : X ⟶ pullback U.ι p)
  (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p)

/-- The diagonal of the refined overlap in source times the original overlap. -/
def commonRetainedGraph : X ⟶
    constantRetainedTarget k p U (commonSourceProjection k p r α) :=
  pullback.lift (𝟙 _) φ (by
    simp only [Category.id_comp, retainedProjection, ← Category.assoc]
    rw [hφ]
    simp only [Category.assoc])

omit [IsSeparated p] [IsOpenImmersion r] in
@[reassoc (attr := simp)] theorem commonRetainedGraph_fst :
    commonRetainedGraph k p r α U φ hφ ≫ pullback.fst _ _ = 𝟙 X :=
  pullback.lift_fst _ _ _
omit [IsSeparated p] [IsOpenImmersion r] in
@[reassoc (attr := simp)] theorem commonRetainedGraph_snd :
    commonRetainedGraph k p r α U φ hφ ≫ pullback.snd _ _ = φ :=
  pullback.lift_snd _ _ _

omit [IsSeparated p] [IsOpenImmersion r] in
/-- This is the literal original graph after the retained open inclusion. -/
theorem commonRetainedGraph_inclusion :
    commonRetainedGraph k p r α U φ hφ ≫
      constantRetainedInclusion k p U (commonSourceProjection k p r α) =
    constantSourceGraph α (projection k p) (r ≫ inclusion k p) := by
  apply pullback.hom_ext <;>
    simp [constantSourceGraph, commonRetainedGraph, Category.assoc, hφ]

omit [IsOpenImmersion r] in
/-- The original lambda diagonal square stays Cartesian on the actual retained common curve. -/
theorem commonRetainedGraph_isPullback :
    IsPullback α (commonRetainedGraph k p r α U φ hφ)
      (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))
      (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
        commonToDiagonal k p r α) := by
  have H : IsPullback (𝟙 X) (commonRetainedGraph k p r α U φ hφ)
      (constantSourceGraph α (projection k p) (r ≫ inclusion k p))
      (constantRetainedInclusion k p U (commonSourceProjection k p r α)) :=
    IsPullback.of_horiz_isIso_mono ⟨by
      simpa only [Category.id_comp] using (commonRetainedGraph_inclusion k p r α U φ hφ).symm⟩
  simpa only [Category.id_comp, commonToDiagonal, constantSourceMapOfEq, constantSourceMap] using
    H.paste_horiz (constantSourceGraph_isPullback α (projection k p) (r ≫ inclusion k p))

/-- The actual retained diagonal ideal is the pullback of the original lambda graph ideal. -/
def commonRetainedGraphIdealIso [Flat α] :
    (Modules.pullback (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
      commonToDiagonal k p r α)).obj (actualIdealLineBundle k p r).val ≅
    Hom.idealModule (commonRetainedGraph k p r α U φ hφ) := by
  let j := Hom.compactificationGraph (projection k p) (r ≫ inclusion k p)
  let v := constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
    commonToDiagonal k p r α
  have : Flat (commonToDiagonal k p r α) :=
    MorphismProperty.of_isPullback (commonToDiagonal_isPullback k p r α).flip inferInstance
  have : Flat v := inferInstance
  have : (Hom.idealModule j).IsQuasicoherent := by
    have := Invertible.finiteLocallyFree_of_isLocallyRankOne
      (actualIdealLineBundle k p r).val (actualIdealLineBundle k p r).property
    exact inferInstanceAs ((actualIdealLineBundle k p r).val.IsQuasicoherent)
  have : IsClosedImmersion j := by dsimp [j, Hom.compactificationGraph]; infer_instance
  have H := commonRetainedGraph_isPullback k p r α U φ hφ
  have : IsClosedImmersion (commonRetainedGraph k p r α U φ hφ) :=
    MorphismProperty.of_isPullback H inferInstance
  let e := Hom.idealPullbackMap j (commonRetainedGraph k p r α U φ hφ) v α H.w
  have : IsIso e := Hom.idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact asIso e

omit [IsOpenImmersion r] in
/-- The comparison retains the original canonical functional, not only its zero support. -/
theorem commonRetainedGraphIdealIso_inclusion [Flat α] :
    (commonRetainedGraphIdealIso k p r α U φ hφ).hom ≫
      Hom.idealInclusion (commonRetainedGraph k p r α U φ hφ) =
    Modules.Hom.pullbackToUnit
      (Hom.idealInclusion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p)))
      (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
        commonToDiagonal k p r α) :=
  Hom.idealPullbackMap_inclusion _ _ _ _ _
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
