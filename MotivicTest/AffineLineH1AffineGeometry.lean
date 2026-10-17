module
public import Motivic.Cohomology.AffineLineH1AffineGeometry
/-! # The actual H1 datum supplies the full affine geometry without extra hypotheses -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology.AffineLineH1LiftData
open AffineLineReducedComplement
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  {F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
  {x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
    F 1 (SmoothSite.affineLine (.of k))} (D : AffineLineH1LiftData F x)


example : ∃ (R : CommRingCat.{u}) (r : Spec R ⟶ D.Y.left)
    (t : closedComplement D.U ⟶ Spec R),
    IsNoetherianRing R ∧ IsOpenImmersion r ∧ t ≫ r = D.complementLift ∧
    IsPullback t (𝟙 _) (r ≫ D.p.left) (inclusion D.U) ∧ Etale (r ≫ D.p.left) :=
  D.exists_affineGeometry

example : D.overlap.left ≅ pullback D.U.ι D.p.left := D.overlapSchemeIso

open Lean in
run_cmd do
  for name in #[``complementLift_isPullback, ``exists_affineGeometry, ``openSpecIso,
      ``overlapSchemeIso, ``overlapSchemeIso_hom_fst, ``overlapSchemeIso_hom_snd,
      ``refinedOverlap_isAffine, ``refinedOverlap_isLocallyNoetherian] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original H1 affine geometry uses only standard foundations."
end Motivic.SheafCohomology.AffineLineH1LiftData
