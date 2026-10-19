/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.AffineLine.PositiveSquare
public import Motivic.Cohomology.AffineLine.OverlapZero

/-! # Ordinary Nisnevich cohomology of the affine line vanishes above degree one -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local instance (U : (line k).Opens) : IsOpenImmersion (openInclusion U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- Arbitrary ordinary abelian Nisnevich coefficients on the original smooth site.
No transfer structure, homotopy invariance, or strict invariance is assumed. -/
theorem affineLine_H_add_two_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (e : H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) F (n + 2) (SmoothSite.affineLine (.of k))) :
    e = 0 := by
  obtain ⟨U, _, hU, V, p, hp, hZ, hV⟩ := exists_affineLine_positive_zero_square F (n + 1) e
  let : Etale p.left := hp
  let : IsIso (pullback.snd p.left (inclusion U)) := hZ
  let j := openInclusion U
  let sq := ordinaryPullbackSquare j p
  have hpb : sq.IsPullback := IsPullback.of_hasPullback _ _
  have hcomp : Set.range (inclusion U) = (Set.range j.left)ᶜ := by
    change Set.range (inclusion U) = (Set.range U.ι)ᶜ
    rw [range_inclusion, Scheme.Opens.range_ι]
  obtain ⟨q, f, hq, hf⟩ := exists_nisnevich_overlap_boundary_lift.{w, u + 1, u}
    sq hpb (inclusion U) hcomp F (n + 1) e hU hV
  obtain ⟨T, hT, hfT⟩ := exists_affineLine_overlap_refinement_zero F U p n f
  let : IsIso (pullback.snd ((SmoothSite.openInclusion V T) ≫ p).left (inclusion U)) := hT
  let : Etale ((SmoothSite.openInclusion V T) ≫ p).left :=
    inferInstanceAs (Etale (T.ι ≫ p.left))
  exact ordinary_eq_zero_of_overlap_refinement.{w, u + 1, u}
    j p (inclusion U) hcomp F (n + 1) e q f hq hf (SmoothSite.openInclusion V T) hfT

end Motivic.SheafCohomology
