/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.RetainedOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.SectionDualDivisor

/-! # Actual section divisors on the original overlap target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S Z : Scheme.{u}} [IsAffine S]
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) (s : Z ⟶ S)
  (U : (Spec (.of (Polynomial k))).Opens) (z : Z ⟶ Spec (.of (Polynomial k)))
  (H : IsPullback (s ≫ r) (𝟙 _) p z)
  (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ)

include H hz in
/-- Actual prescribed boundary sections yield whole finite flat zeros on the original overlap. -/
theorem actualSectionDivisor_finite_mono_flat
    (L : LineBundle (diagonalAmbient k p r))
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) a)] :
    let q := (r ≫ inclusion k p) ≫ projection k p
    let j := constantRetainedInclusion k p U q
    let f := Hom.pullbackToUnit (sectionDualFunctional _ L a) j
    IsFinite (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p)) ∧
      Mono f ∧ Flat (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p)) := by
  let q := (r ≫ inclusion k p) ≫ projection k p
  let j := constantRetainedInclusion k p U q
  have := constantRetainedTarget_quasiAffine k p U q
  have : SmoothOfRelativeDimension 1 (j ≫ pullback.fst q (projection k p)) := by
    dsimp only [j]
    rw [constantRetainedInclusion_fst]
    exact constantRetainedTarget_smooth k p U q
  exact sectionDualFunctional_finite_mono_flat_on_open (diagonalBoundaryMap k p r s)
    (pullback.fst q (projection k p)) j L a
    (diagonalBoundary_retained_cover k p r s U z H hz)
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
