module
public import Motivic.Cohomology.A1.LocalVanishing.H1.AffineGeometry
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.SiteMaps
/-! # Original H1 source and overlap comparisons for the actual pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.AffineLineEtaleCompactification
universe w u
namespace Motivic.SheafCohomology.AffineLineH1LiftData
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  {F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
  {x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
    F 1 (SmoothSite.affineLine (.of k))} (D : AffineLineH1LiftData F x)
  (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r]

instance pencilRefinement_quasiCompact : QuasiCompact r := inferInstance

/-- The affine refinement is an actual map to the original smooth-site object. -/
def pencilRefinementSiteMap : diagonalSourceSite k D.p.left r ⟶ D.Y :=
  SmoothSite.homMk r (by
    change r ≫ D.Y.hom = (r ≫ inclusion k D.p.left) ≫ projection k D.p.left
    rw [Category.assoc, inclusion_projection]
    simpa only [Category.assoc, SmoothSite.affineLine_hom,
      Scheme.PolynomialLaurent.polynomialProjection] using congrArg (fun f => r ≫ f)
      (MorphismProperty.Over.w D.p).symm)

abbrev pencilOverlap := (D.refinedSquare (D.pencilRefinementSiteMap R r)).X₁
abbrev pencilSourceAlpha : (D.pencilOverlap R r).left ⟶ Spec R :=
  (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₃.left
abbrev pencilSourceBeta : (D.pencilOverlap R r).left ⟶ Spec Γ(D.U.toScheme, ⊤) :=
  (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₂.left ≫ D.openSpecIso.hom
abbrev pencilSourceGraphMap : (D.pencilOverlap R r).left ⟶ pullback D.U.ι D.p.left :=
  (D.overlapMap (D.pencilRefinementSiteMap R r)).left ≫ D.overlapSchemeIso.hom

/-- Native scheme pullback comparison for the refined, not replaced, overlap. -/
def pencilOverlapSchemeIso : (D.pencilOverlap R r).left ≅ pullback D.U.ι (r ≫ D.p.left) :=
  PreservesPullback.iso (SmoothSite.forgetScheme (Spec (.of k)))
    (openInclusion D.U) (D.pencilRefinementSiteMap R r ≫ D.p)

@[reassoc (attr := simp)] theorem pencilOverlapSchemeIso_hom_fst :
    (D.pencilOverlapSchemeIso R r).hom ≫ pullback.fst _ _ =
      (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₂.left :=
  PreservesPullback.iso_hom_fst _ _ _
@[reassoc (attr := simp)] theorem pencilOverlapSchemeIso_hom_snd :
    (D.pencilOverlapSchemeIso R r).hom ≫ pullback.snd _ _ = D.pencilSourceAlpha R r :=
  PreservesPullback.iso_hom_snd _ _ _

instance pencilSourceAlpha_open : IsOpenImmersion (D.pencilSourceAlpha R r) := by
  rw [← D.pencilOverlapSchemeIso_hom_snd R r]
  infer_instance
instance pencilSourceAlpha_quasiCompact : QuasiCompact (D.pencilSourceAlpha R r) :=
  SmoothSite.quasiCompact_hom _
instance pencilSourceBeta_etale : Etale (D.pencilSourceBeta R r) := by
  dsimp only [pencilSourceBeta]
  rw [← D.pencilOverlapSchemeIso_hom_fst R r]
  infer_instance
instance pencilOverlap_affine : IsAffine (D.pencilOverlap R r).left := by
  let : IsAffine (pullback D.U.ι (r ≫ D.p.left)) := D.refinedOverlap_isAffine R r
  exact IsAffine.of_isIso (D.pencilOverlapSchemeIso R r).hom

/-- The two unchanged source coordinates commute literally. -/
theorem pencilSourceEq :
    D.pencilSourceAlpha R r ≫ r ≫ D.p.left = D.pencilSourceBeta R r ≫ D.openSpecMap := by
  simp only [pencilSourceBeta, openSpecMap, Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [MorphismProperty.Comma.comp_left, pencilSourceAlpha, pencilOverlap,
    refinedSquare, openInclusion_left, pencilRefinementSiteMap,
    SmoothSite.homMk_left, Category.assoc] using (congrArg (fun f => f.left)
    (D.refinedSquare (D.pencilRefinementSiteMap R r)).fac).symm

/-- The graph map retains the original target coordinate of the overlap. -/
theorem pencilGraphEq :
    D.pencilSourceGraphMap R r ≫ retainedInclusion k D.p.left D.U =
      D.pencilSourceAlpha R r ≫ r ≫ inclusion k D.p.left := by
  dsimp only [pencilSourceGraphMap, retainedInclusion]
  rw [Category.assoc, ← Category.assoc D.overlapSchemeIso.hom,
    D.overlapSchemeIso_hom_snd]
  have h := congrArg (fun f => f.left) (D.overlapMap_snd (D.pencilRefinementSiteMap R r))
  simpa only [MorphismProperty.Comma.comp_left, pencilSourceAlpha, pencilOverlap,
    refinedSquare, openInclusion_left, pencilRefinementSiteMap,
    SmoothSite.homMk_left, Category.assoc] using
      congrArg (fun f => f ≫ inclusion k D.p.left) h

/-- Canonical pencil common source is the original refined H1 overlap. -/
def pencilCommonSourceIso : commonSourceSite k D.p.left r (D.pencilSourceAlpha R r) ≅
    D.pencilOverlap R r :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ (D.pencilOverlap R r).hom = _
    rw [Category.id_comp]
    exact (MorphismProperty.Over.w
      (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₃).symm)

/-- The fixed pencil source presents the whole original U, not a smaller open. -/
def pencilFixedSourceIso : fixedSourceSite k D.openSpecMap ≅ openObject D.U :=
  MorphismProperty.Over.isoMk D.openSpecIso.symm (by
    change D.openSpecIso.inv ≫ (D.U.ι ≫ Scheme.Hom.boundaryLineProjection k) = _
    rfl)

/-- The pencil target is the original H1 overlap. -/
def pencilRetainedTargetIso : retainedTargetSite k D.p.left D.U ≅ D.overlap :=
  MorphismProperty.Over.isoMk D.overlapSchemeIso.symm (by
    change D.overlapSchemeIso.inv ≫ D.overlap.hom = retainedProjection k D.p.left D.U
    rw [← MorphismProperty.Over.w D.square.f₁₃]
    have he := D.overlapSchemeIso_hom_snd
    have hi : D.overlapSchemeIso.inv ≫ D.square.f₁₃.left = pullback.snd D.U.ι D.p.left := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hi]
    simp only [retainedProjection, retainedInclusion, Category.assoc, inclusion_projection]
    simpa only [Category.assoc, SmoothSite.affineLine_hom,
      Scheme.PolynomialLaurent.polynomialProjection] using
      congrArg (fun f => pullback.snd D.U.ι D.p.left ≫ f)
        (MorphismProperty.Over.w D.p).symm)

end Motivic.SheafCohomology.AffineLineH1LiftData
