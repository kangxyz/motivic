/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.H1.Pencil.Inputs
/-! # Literal endpoint comparisons for the original H1 square -/
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


/-- The lambda source leg is unchanged under the native common-source comparison. -/
theorem pencilAlpha_transport :
    (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₃ ≫ 𝟙 _ =
      (D.pencilCommonSourceIso R r).inv ≫ pencilAlpha k D.p.left r (D.pencilSourceAlpha R r) := by
  apply MorphismProperty.Over.Hom.ext
  change D.pencilSourceAlpha R r ≫ 𝟙 _ = 𝟙 _ ≫ D.pencilSourceAlpha R r
  simp only [Category.comp_id, Category.id_comp]

/-- The psi leg retains the unchanged open through its canonical Spec presentation. -/
theorem pencilBeta_transport :
    (D.refinedSquare (D.pencilRefinementSiteMap R r)).f₁₂ ≫ D.pencilFixedSourceIso.inv =
      (D.pencilCommonSourceIso R r).inv ≫
        pencilBeta k D.p.left r D.openSpecMap (D.pencilSourceAlpha R r)
          (D.pencilSourceBeta R r) (D.pencilSourceEq R r) := by
  apply MorphismProperty.Over.Hom.ext
  change D.pencilSourceBeta R r = 𝟙 _ ≫ D.pencilSourceBeta R r
  exact (Category.id_comp _).symm

/-- The graph endpoint lands in the original H1 overlap with both original projections. -/
theorem pencilGraph_transport :
    (D.pencilCommonSourceIso R r).inv ≫
      pencilGraphMap k D.p.left r (D.pencilSourceAlpha R r) D.U
        (D.pencilSourceGraphMap R r) (D.pencilGraphEq R r) ≫
      D.pencilRetainedTargetIso.hom = D.overlapMap (D.pencilRefinementSiteMap R r) := by
  apply MorphismProperty.Over.Hom.ext
  change (𝟙 _ ≫ ((D.overlapMap (D.pencilRefinementSiteMap R r)).left ≫
    D.overlapSchemeIso.hom)) ≫ D.overlapSchemeIso.inv = _
  simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Motivic.SheafCohomology.AffineLineH1LiftData
