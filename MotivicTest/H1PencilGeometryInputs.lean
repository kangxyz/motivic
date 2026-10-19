module
public import Motivic.Cohomology.A1.LocalVanishing.H1.Pencil.Transport
/-! # Native original-H1 pencil input and endpoint comparison audit -/
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

example :
    (D.pencilCommonSourceIso R r).inv ≫
      pencilGraphMap k D.p.left r (D.pencilSourceAlpha R r) D.U
        (D.pencilSourceGraphMap R r) (D.pencilGraphEq R r) ≫
      D.pencilRetainedTargetIso.hom = D.overlapMap (D.pencilRefinementSiteMap R r) :=
  D.pencilGraph_transport R r

open Lean in
run_cmd do
  for name in #[``pencilRefinementSiteMap, ``pencilSourceEq, ``pencilGraphEq,
      ``pencilCommonSourceIso, ``pencilFixedSourceIso, ``pencilRetainedTargetIso,
      ``pencilSourceAlpha_open, ``pencilSourceBeta_etale, ``pencilOverlap_affine,
      ``pencilAlpha_transport, ``pencilBeta_transport, ``pencilGraph_transport] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Native original-H1 pencil comparisons use only standard foundations."

end Motivic.SheafCohomology.AffineLineH1LiftData
