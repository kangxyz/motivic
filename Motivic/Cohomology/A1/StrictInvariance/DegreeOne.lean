/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvariance.DegreeInduction
public import Motivic.Cohomology.A1.Cartier.Restriction.H1Restriction

/-! # Original degree-one affine-line invariance over infinite perfect fields

The proved Cartier H1 puncture monomorphism closes the finite local-rank
induction in degree one. Actual marked test-object fibers detect the first
higher direct image, and the finite Leray window then proves invertibility of
the original ordinary H1 projection. No higher-degree puncture monomorphism,
current-degree homotopy invariance, or finite-field descent is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] [Infinite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original puncture-restriction family in degree one is proved at every
full field-valued smooth Cartier mark, with no boundary epimorphism premise. -/
theorem smoothCartierPunctureRestrictionMono_one
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    SmoothCartierPunctureRestrictionMono F 1 := by
  intro Y K _ b p Z i hi hI hs hb W hW
  let : IsClosedImmersion i := hi
  let : Smooth (i ≫ Y.hom) := hs
  let : IsOpenImmersion (SmoothSite.openInclusion Y W).left :=
    inferInstanceAs (IsOpenImmersion W.ι)
  apply pointedCylinderRestriction_H1_mono_of_cartier Y F hF i hI
    (SmoothSite.openInclusion Y W) _ K b p hb
  change Set.range i = (Set.range W.ι)ᶜ
  rw [Scheme.Opens.range_ι]
  exact hW

local instance degreeOneRankHasExt (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The first higher image of the original affine-line projection vanishes for
HI transfer coefficients over an infinite perfect field. -/
theorem projectionHigherImage_one_isZero [PerfectField k]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsZero (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived 1).obj
      ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
        ((SheafWithTransfers.toSheaf k).obj F))) := by
  apply projectionHigherImage_isZero_of_puncture_mono F hF 0
    (fun q hq hq1 => False.elim (by omega))
    (smoothCartierPunctureRestrictionMono_one F hF) X

end Motivic.FiniteEtaleSite

namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType _root_.Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] [Infinite k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local instance degreeOneProjectionHasExt (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.EtaleSeparatedFiniteType.nisnevichTopology Y) AddCommGrpCat.{u +
        1}) :=
  hasExt_of_enoughInjectives _

/-- HI transfer coefficients give homotopy invariance of original ordinary H1
via the literal projection, over an infinite perfect field. -/
theorem degreeOne_isInvariant (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) :
    A1.IsInvariant (.of k)
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) 1) := by
  intro X
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply a1_projection_bijective_of_rightDerived_window X F hF 1
  intro q hq hq1
  have hqeq : q = 1 := by omega
  subst q
  exact projectionHigherImage_one_isZero F hF X

/-- The same original degree-one invariance on the canonical cohomology
presheaf with transfers, through its graph comparison. -/
theorem degreeOne_withTransfers_isA1Invariant (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) :
    (SheafCohomology.withTransfers k F 1).IsA1Invariant := by
  intro X
  exact (NatIso.isIso_map_iff (SheafCohomology.withTransfersGraphIso k F 1)
    (SmoothSite.a1Projection (.of k) X).op).mpr (degreeOne_isInvariant F hF X)

end Motivic.SheafWithTransfers
