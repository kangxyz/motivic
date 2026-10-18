/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCartierPositiveRestrictionInputs
public import Motivic.Cohomology.A1.StrictA1DegreeInduction

/-! # Strict invariance conditional on two original coefficient producers

Over a perfect field, original PST integral-affine local zero and original
canonical boundary Epi suffice for the actual strict NST endpoint. Both families
remain explicit mathematical inputs. No finite-field producer, HI of arbitrary
PST sheafification, or unconditional finite-field strict theorem is asserted.
The existing rank, degree and finite Leray assembly is reused unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite.CoefficientInputs

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The degree-one puncture family uses only original coefficient local zero
and canonical Epi; no degree-one cohomological HI is supplied. -/
theorem smoothCartierPunctureRestrictionMono_one
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : OriginalPresheaf.CanonicalBoundaryEpi k)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    SmoothCartierPunctureRestrictionMono F 1 := by
  intro Y K _ b p Z i hi hI hs hb W hW
  let : IsClosedImmersion i := hi
  let : Smooth (i ≫ Y.hom) := hs
  let : IsOpenImmersion (SmoothSite.openInclusion Y W).left :=
    inferInstanceAs (IsOpenImmersion W.ι)
  apply pointedCylinderRestriction_H1_mono_of_cartier_of_boundary_epi
    hD Y F hF (fun X => contractionToBoundary_epi_of_canonicalBoundaryEpi hE X F hF)
    i hI (SmoothSite.openInclusion Y W) _ K b p hb
  change Set.range i = (Set.range W.ι)ᶜ
  rw [Scheme.Opens.range_ι]
  exact hW

/-- The exact full-marked puncture family follows from the two coefficient
inputs and strictly lower degrees for all HI coefficients, including F_-1. -/
theorem smoothCartierPunctureRestrictionMono_of_lower_degrees
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : OriginalPresheaf.CanonicalBoundaryEpi k)
    (n : ℕ)
    (hLow : ∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
      ∀ q : ℕ, 0 < q → q < n + 1 →
        (SheafCohomology.withTransfers k G q).IsA1Invariant)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    SmoothCartierPunctureRestrictionMono F (n + 1) := by
  cases n with
  | zero => exact smoothCartierPunctureRestrictionMono_one hD hE F hF
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
    apply pointedCylinderRestriction_positive_mono_of_cartier hD hE Y F hF n
      (hLow F hF) hContract i hI (SmoothSite.openInclusion Y W) _ K b p hb
    change Set.range i = (Set.range W.ι)ᶜ
    rw [Scheme.Opens.range_ι]
    exact hW

end Motivic.FiniteEtaleSite.CoefficientInputs

namespace Motivic.SheafWithTransfers
variable {k : Type u} [Field k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Conditional strict invariance of the literal ordinary projection over any
perfect field. The two original PST producer contracts remain explicit inputs. -/
theorem isStrictA1Invariant_of_coefficient_inputs
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : FiniteEtaleSite.OriginalPresheaf.CanonicalBoundaryEpi k)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    F.IsStrictA1Invariant :=
  isStrictA1Invariant_of_smoothCartierPunctureRestrictionMono
    (FiniteEtaleSite.CoefficientInputs.smoothCartierPunctureRestrictionMono_of_lower_degrees
      hD hE) F hF

end Motivic.SheafWithTransfers
