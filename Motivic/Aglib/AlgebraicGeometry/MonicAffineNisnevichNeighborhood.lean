/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.MonicNisnevichSectionSpread
public import Motivic.Aglib.AlgebraicGeometry.AffineEtaleClosedSectionNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Actual affine neighborhoods of the entire localized monic divisor -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Polynomial Motivic
universe u
namespace AlgebraicGeometry.Scheme.GenericSection
open PolynomialOpenQuotient
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- The neighborhood factors through the original affine Nisnevich cover and is
an isomorphism over the full, possibly nonreduced monic closed subscheme. -/
theorem exists_affine_monic_neighborhood (f : R[X]) (hf : f.Monic)
    {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ Spec (.of R[X])) [Etale q]
    (hq : Presieve.singleton q ∈ Nisnevich.precoverage (Spec (.of R[X]))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (W : Scheme.{u}) (p : W ⟶ Spec (.of (Localization.Away r)[X]))
      (a : W ⟶ Y), IsAffine W ∧ Etale p ∧
        a ≫ q = p ≫ lineAwayMap R r ∧
        IsIso (pullback.snd p (inclusion (f.map (algebraMap R (Localization.Away r))))) := by
  obtain ⟨r, hr, a, ha⟩ := exists_monic_lift_after_localization R f hf q hq
  let b := lineAwayMap R r
  let z := inclusion (f.map (algebraMap R (Localization.Away r)))
  let p := pullback.snd q b
  let s : _ ⟶ pullback p z := pullback.lift a (𝟙 _) (by simpa using ha)
  have hs : s ≫ pullback.snd p z = 𝟙 _ := pullback.lift_snd _ _ _
  obtain ⟨t, _, _, ht, hi⟩ := Hom.exists_basicOpen_iso_over_closed_of_section p z s hs
  let W := (pullback q b).basicOpen t
  exact ⟨r, hr, W.toScheme, W.ι ≫ p, W.ι ≫ pullback.fst q b, ht,
    inferInstance, by simp only [Category.assoc, pullback.condition]; rfl, hi⟩

end AlgebraicGeometry.Scheme.GenericSection
