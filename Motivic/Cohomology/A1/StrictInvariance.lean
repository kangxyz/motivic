/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.DegreeOne
public import Motivic.Cohomology.A1.PointedCartierPositiveRestriction

/-! # Strict affine-line invariance over infinite perfect fields

The original smooth Cartier puncture-monomorphism family is discharged by the
proved degree-one restriction and the higher-degree restriction. Its lower-degree
induction hypothesis ranges over every HI transfer sheaf. In particular, it
applies to the actual contraction, whose ordinary coefficient-level homotopy
invariance is proved independently. No current-degree HI or puncture-monomorphism
family is supplied to the resulting strict-invariance theorem.

Every degree retains the original ordinary cohomology projection. This module
does not establish finite-field descent.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] [Infinite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original puncture-monomorphism family follows from strictly lower
cohomology degrees for all HI coefficients, including the actual contraction. -/
theorem smoothCartierPunctureRestrictionMono_of_lower_degrees
    (n : ℕ)
    (hLow : ∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
      ∀ q : ℕ, 0 < q → q < n + 1 →
        (SheafCohomology.withTransfers k G q).IsA1Invariant)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    SmoothCartierPunctureRestrictionMono F (n + 1) := by
  cases n with
  | zero => exact smoothCartierPunctureRestrictionMono_one F hF
  | succ n =>
    intro Y K _ b p Z i hi hI hs hb W hW
    let : IsClosedImmersion i := hi
    let : Smooth (i ≫ Y.hom) := hs
    let : IsOpenImmersion (SmoothSite.openInclusion Y W).left :=
      inferInstanceAs (IsOpenImmersion W.ι)
    have hContract : (SheafCohomology.withTransfers k
        (SheafWithTransfers.contraction F hF) (n + 1)).IsA1Invariant :=
      hLow (SheafWithTransfers.contraction F hF)
        (SheafWithTransfers.contraction_isA1Invariant F hF) (n + 1)
        (Nat.succ_pos n) (by omega)
    apply pointedCylinderRestriction_positive_mono_of_cartier Y F hF n
      (hLow F hF) hContract i hI (SmoothSite.openInclusion Y W) _ K b p hb
    change Set.range i = (Set.range W.ι)ᶜ
    rw [Scheme.Opens.range_ι]
    exact hW

end Motivic.FiniteEtaleSite

namespace Motivic.SheafWithTransfers

variable {k : Type u} [Field k] [Infinite k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every HI Nisnevich sheaf with transfers is strictly affine-line invariant
over an infinite perfect field, for the actual ordinary projection in every degree. -/
theorem isStrictA1Invariant_of_isA1Invariant (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) : F.IsStrictA1Invariant :=
  isStrictA1Invariant_of_smoothCartierPunctureRestrictionMono
    FiniteEtaleSite.smoothCartierPunctureRestrictionMono_of_lower_degrees F hF

/-- Over an infinite perfect field, strict invariance of the original ordinary
cohomology projections is equivalent to ordinary HI of the transfer coefficient. -/
theorem isStrictA1Invariant_iff_isA1Invariant (F : SheafWithTransfers.{u + 1} k) :
    F.IsStrictA1Invariant ↔ F.obj.IsA1Invariant :=
  ⟨fun hF => hF.isA1Invariant, isStrictA1Invariant_of_isA1Invariant F⟩

end Motivic.SheafWithTransfers
