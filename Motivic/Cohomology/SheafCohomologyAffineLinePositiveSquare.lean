/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyArtinianNeighborhoodZero
public import Motivic.Cohomology.SheafCohomologyH1AffineLineLocalLifts
public import Motivic.Cohomology.SheafCohomologyGenericOpen

/-! # A constructed Nisnevich square killing a positive affine-line class on both legs -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology
open AffineLineReducedComplement
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Both zero restrictions and the isomorphism over the whole complement are
constructed from the actual class, for arbitrary ordinary coefficients. -/
theorem exists_affineLine_positive_zero_square
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (e : H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) F (n + 1) (SmoothSite.affineLine (.of k))) :
    ∃ (U : (line k).Opens), genericPoint (line k) ∈ U ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 1)).map (openInclusion U).op e = 0 ∧
      ∃ (Y : SmoothSite (Spec (.of k))) (p : Y ⟶ SmoothSite.affineLine (.of k)),
        Etale p.left ∧ IsIso (pullback.snd p.left (inclusion U)) ∧
        (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
          F (n + 1)).map p.op e = 0 := by
  let : IsIntegral (SmoothSite.affineLine (.of k)).left :=
    inferInstanceAs (IsIntegral (Spec (.of (Polynomial k))))
  obtain ⟨U, hU, heU⟩ := exists_generic_open_restriction_eq_zero F n
    (SmoothSite.affineLine (.of k)) e
  let : IsLocallyArtinian (closedComplement U) := affineLine_complement_isLocallyArtinian U hU
  obtain ⟨Y, p, hp, hZ, heY⟩ := exists_etale_neighborhood_restriction_eq_zero F n
    (SmoothSite.affineLine (.of k)) e (inclusion U)
  exact ⟨U, hU, heU, Y, p, hp, hZ, heY⟩

end Motivic.SheafCohomology
