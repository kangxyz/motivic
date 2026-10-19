/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.H1.GenericOpenLift
public import Motivic.Cohomology.Sheaf.ArtinianNeighborhoodLift
public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineReducedComplement

/-! # Constructed generic-open and étale-neighborhood lifts on the affine line -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology

open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement

variable {k : Type u} [Field k]

/-- The entire reduced complement of a generic-containing open in the affine
line is locally Artinian, not just a selected collection of closed points. -/
theorem affineLine_complement_isLocallyArtinian
    (U : (line k).Opens) (hU : genericPoint (line k) ∈ U) :
    IsLocallyArtinian (closedComplement U) := by
  obtain ⟨f, hf, hD⟩ := exists_nonzero_basicOpen U hU
  have := finite_quotient_of_basicOpen U hf hD
  have : IsArtinianRing (Polynomial k ⧸ complementIdeal U) :=
    IsArtinianRing.of_finite k _
  exact inferInstanceAs
    (IsLocallyArtinian (Spec (.of (Polynomial k ⧸ complementIdeal U))))

variable
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every actual ordinary H¹ class on the affine line admits its original
quotient representative with actual lifts on a constructed generic open and
on a constructed étale neighborhood isomorphic over the full reduced complement. -/
theorem exists_affineLine_affine_local_lifts_of_h_one
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F 1 (SmoothSite.affineLine (.of k))) :
    ∃ (s : (cokernel (Injective.ι F)).obj.obj (op (SmoothSite.affineLine (.of k)))),
      injectiveSectionBoundary (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (SmoothSite.affineLine (.of k)) s = x ∧
    ∃ (U : (line k).Opens), genericPoint (line k) ∈ U ∧ IsAffineOpen U ∧
    ∃ (lU : (Injective.under F).obj.obj (op (openObject U))),
      (cokernel.π (Injective.ι F)).hom.app (op (openObject U)) lU =
        (cokernel (Injective.ι F)).obj.map (openInclusion U).op s ∧
    ∃ (Y : SmoothSite (Spec (.of k))) (p : Y ⟶ SmoothSite.affineLine (.of k)),
      Etale p.left ∧ IsIso (pullback.snd p.left (inclusion U)) ∧
    ∃ lY : (Injective.under F).obj.obj (op Y),
      (cokernel.π (Injective.ι F)).hom.app (op Y) lY =
        (cokernel (Injective.ι F)).obj.map p.op s := by
  have : IsIntegral (SmoothSite.affineLine (.of k)).left :=
    inferInstanceAs (IsIntegral (line k))
  obtain ⟨s, hs, A, j, hAff, hj, hη, lA, hlA⟩ :=
    exists_generic_affine_open_lift_of_h_one F (SmoothSite.affineLine (.of k)) x
  let U : (line k).Opens := j.left.opensRange
  let a : U.toScheme ⟶ A.left := IsOpenImmersion.lift j.left U.ι (by
    rw [Scheme.Opens.range_ι]
    exact fun _ h ↦ h)
  have ha : a ≫ j.left = U.ι := IsOpenImmersion.lift_fac j.left U.ι _
  let b : openObject U ⟶ A := SmoothSite.homMk a (by
    rw [← MorphismProperty.Over.w j, ← Category.assoc, ha]
    rfl)
  have hb : b ≫ j = openInclusion U := by
    apply MorphismProperty.Over.Hom.ext
    exact ha
  have hU : genericPoint (line k) ∈ U := hη
  have := affineLine_complement_isLocallyArtinian U hU
  obtain ⟨Y, p, hp, hZ, lY, hlY⟩ := exists_etale_neighborhood_lift
    (cokernel.π (Injective.ι F)) (SmoothSite.affineLine (.of k)) s (inclusion U)
  refine ⟨s, hs, U, hU, isAffineOpen_opensRange j.left,
    (Injective.under F).obj.map b.op lA, ?_, Y, p, hp, hZ, lY, hlY⟩
  rw [(cokernel.π (Injective.ι F)).hom.naturality_apply, hlA,
    ← Functor.map_comp_apply, ← op_comp, hb]

/-- The original local-lift endpoint, retaining its statement for existing consumers. -/
theorem exists_affineLine_local_lifts_of_h_one
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F 1 (SmoothSite.affineLine (.of k))) :
    ∃ (s : (cokernel (Injective.ι F)).obj.obj (op (SmoothSite.affineLine (.of k)))),
      injectiveSectionBoundary (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (SmoothSite.affineLine (.of k)) s = x ∧
    ∃ (U : (line k).Opens), genericPoint (line k) ∈ U ∧
    ∃ (lU : (Injective.under F).obj.obj (op (openObject U))),
      (cokernel.π (Injective.ι F)).hom.app (op (openObject U)) lU =
        (cokernel (Injective.ι F)).obj.map (openInclusion U).op s ∧
    ∃ (Y : SmoothSite (Spec (.of k))) (p : Y ⟶ SmoothSite.affineLine (.of k)),
      Etale p.left ∧ IsIso (pullback.snd p.left (inclusion U)) ∧
    ∃ lY : (Injective.under F).obj.obj (op Y),
      (cokernel.π (Injective.ι F)).hom.app (op Y) lY =
        (cokernel (Injective.ι F)).obj.map p.op s := by
  obtain ⟨s, hs, U, hU, _, lU, hlU, Y, p, hp, hZ, lY, hlY⟩ :=
    exists_affineLine_affine_local_lifts_of_h_one F x
  exact ⟨s, hs, U, hU, lU, hlU, Y, p, hp, hZ, lY, hlY⟩

end Motivic.SheafCohomology
