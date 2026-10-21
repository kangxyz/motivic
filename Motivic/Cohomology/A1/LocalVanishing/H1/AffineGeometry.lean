/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.Sheaf.H1.AffineLineGeometryConsumer
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineBoundarySpec
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian
/-! # Actual affine presentations of the original affine-line H1 lifting geometry -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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

local instance : IsAffine (SmoothSite.affineLine (.of k)).left :=
  inferInstanceAs (IsAffine (Spec (.of (Polynomial k))))
local instance : IsAffine D.U.toScheme := D.affine_open

/-- The full original complement lifts, using the given complement isomorphism. -/
def complementLift : closedComplement D.U ⟶ D.Y.left :=
  inv (pullback.snd D.p.left (inclusion D.U)) ≫ pullback.fst D.p.left (inclusion D.U)

@[reassoc (attr := simp)] theorem complementLift_comp :
    D.complementLift ≫ D.p.left = inclusion D.U := by
  simp only [complementLift, Category.assoc, pullback.condition]
  simp

/-- No point of the original complement is discarded by this lift. -/
theorem complementLift_isPullback :
    IsPullback D.complementLift (𝟙 _) D.p.left (inclusion D.U) := by
  apply IsPullback.of_iso_pullback ⟨by simp⟩ (asIso (pullback.snd D.p.left (inclusion D.U))).symm
  · rfl
  · simp

/-- A genuine Noetherian affine-Spec refinement retains the entire original complement. -/
theorem exists_affineGeometry :
    ∃ (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left)
      (t : closedComplement D.U ⟶ Spec R),
      IsNoetherianRing R ∧ IsOpenImmersion r ∧ t ≫ r = D.complementLift ∧
      IsPullback t (𝟙 _) (r ≫ D.p.left) (inclusion D.U) ∧ Etale (r ≫ D.p.left) := by
  let : IsFinite (projection D.U) :=
    finite_projection D.U D.generic_mem
  exact Scheme.exists_noetherian_spec_etale_boundary_refinement D.p.left
    (inclusion D.U) D.complementLift D.complementLift_isPullback
    (projection D.U)

/-- The fixed open itself, not a smaller open, in its canonical affine presentation. -/
def openSpecIso : D.U.toScheme ≅ Spec Γ(D.U.toScheme, ⊤) := D.U.toScheme.isoSpec

/-- Original inclusion of the canonical fixed-open affine presentation. -/
def openSpecMap : Spec Γ(D.U.toScheme, ⊤) ⟶ line k := D.openSpecIso.inv ≫ D.U.ι

instance : IsOpenImmersion D.openSpecMap := by dsimp [openSpecMap]; infer_instance
instance : IsNoetherianRing Γ(D.U.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top D.U.toScheme⟩

/-- The original smooth-site overlap is compared to its actual scheme pullback. -/
def overlapSchemeIso : D.overlap.left ≅ pullback D.U.ι D.p.left :=
  PreservesPullback.iso (SmoothSite.forgetScheme (Spec (.of k))) (openInclusion D.U) D.p

@[reassoc (attr := simp)] theorem overlapSchemeIso_hom_fst :
    D.overlapSchemeIso.hom ≫ pullback.fst D.U.ι D.p.left = D.square.f₁₂.left :=
  PreservesPullback.iso_hom_fst _ _ _

@[reassoc (attr := simp)] theorem overlapSchemeIso_hom_snd :
    D.overlapSchemeIso.hom ≫ pullback.snd D.U.ι D.p.left = D.square.f₁₃.left :=
  PreservesPullback.iso_hom_snd _ _ _

/-- Affineness is asserted for the genuine refined overlap, not for the original Y. -/
theorem refinedOverlap_isAffine (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left) :
    IsAffine (pullback D.U.ι (r ≫ D.p.left)) := by infer_instance

/-- Its Noetherianity follows from the unchanged Noetherian affine-line base. -/
theorem refinedOverlap_isLocallyNoetherian (R : CommRingCat.{u})
    (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r] :
    IsLocallyNoetherian (pullback D.U.ι (r ≫ D.p.left)) := by
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst D.U.ι (r ≫ D.p.left))

/-- The refined affine overlap is genuinely Noetherian. -/
theorem refinedOverlap_isNoetherian (R : CommRingCat.{u})
    (r : Spec R ⟶ D.Y.left) [IsOpenImmersion r] :
    IsNoetherian (pullback D.U.ι (r ≫ D.p.left)) := by
  let : IsAffine (pullback D.U.ι (r ≫ D.p.left)) := D.refinedOverlap_isAffine R r
  let : IsLocallyNoetherian (pullback D.U.ι (r ≫ D.p.left)) :=
    D.refinedOverlap_isLocallyNoetherian R r
  exact ⟨⟩

/-- The original overlap is Noetherian, without incorrectly asserting it affine. -/
theorem overlap_isNoetherian : IsNoetherian D.overlap.left := inferInstance

end Motivic.SheafCohomology.AffineLineH1LiftData
