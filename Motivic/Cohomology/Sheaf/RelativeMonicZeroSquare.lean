/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Monic.NeighborhoodZero
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Actual positive zero squares after shrinking only the relative-line base -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Algebra.Smooth _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- The original positive class is zero on the complement of an actual monic
divisor after a nonzero localization of the base, not of the curve parameter. -/
theorem exists_relative_monic_open_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 1) (lineSite (k := k) (R := R))) :
    ∃ r : R, r ≠ 0 ∧ ∃ f : (Localization.Away r)[X], f.Monic ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 1)).map
          (openInclusion f ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op
            e = 0 := by
  let L := lineSite (k := k) (R := R)
  let : IsIntegral L.left := inferInstanceAs (IsIntegral (Spec (.of R[X])))
  obtain ⟨W, hW, heW⟩ := exists_generic_open_restriction_eq_zero F n L e
  obtain ⟨r, hr, g, hg, _, hWg⟩ :=
    AffineLineOpenMonicShrinking.exists_monic_punctured_open R W ⟨_, hW⟩
  let A := Localization.Away r
  let φ : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let v := openMapOfLE φ W (principalOpen (X * g)) hWg
  have hv : openInclusion (X * g) ≫ lineMap φ = v ≫ SmoothSite.openInclusion L W := by
    apply MorphismProperty.Over.Hom.ext
    exact (openMapOfLE_inclusion φ W (principalOpen (X * g)) hWg).symm
  refine ⟨r, hr, X * g, monic_X.mul hg, ?_⟩
  rw [hv, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact (congrArg ((presheaf _ F (n + 1)).map v.op) heW).trans (map_zero _)

/-- An already-zero monic complement and the original closed-neighborhood
producer give an actual Nisnevich zero square after one further base localization. -/
theorem exists_relative_monic_positive_zero_square
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (f : R[X]) (hf : f.Monic)
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 1) (lineSite (k := k) (R := R)))
    (hU : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 1)).map (openInclusion f).op e = 0) :
    ∃ r : R, r ≠ 0 ∧ ∃ (Y : SmoothSite (Spec (.of k)))
      (p : Y ⟶ lineSite (k := k) (R := Localization.Away r)),
      IsAffine Y.left ∧ Etale p.left ∧
      IsIso (pullback.snd p.left (inclusion (f.map (algebraMap R (Localization.Away r))))) ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 1)).map (openInclusion (f.map (algebraMap R (Localization.Away r)))).op
          ((presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
            F (n + 1)).map (lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e) = 0 ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 1)).map
          (p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e = 0 := by
  obtain ⟨r, hr, Y, p, hY, hp, hZ, hV⟩ :=
    exists_relative_monic_neighborhood_restriction_eq_zero F n f hf e
  let A := Localization.Away r
  let φ : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  have hpre : principalOpen (f.map (algebraMap R A)) ≤ (lineMap φ).left ⁻¹ᵁ principalOpen f := by
    intro x hx
    exact hx
  let v := openMapOfLE φ (principalOpen f) (principalOpen (f.map (algebraMap R A))) hpre
  have hv : openInclusion (f.map (algebraMap R A)) ≫ lineMap φ = v ≫ openInclusion f := by
    apply MorphismProperty.Over.Hom.ext
    exact (openMapOfLE_inclusion φ (principalOpen f) _ hpre).symm
  refine ⟨r, hr, Y, p, hY, hp, hZ, ?_, hV⟩
  change (presheaf _ F (n + 1)).map (openInclusion (f.map (algebraMap R A))).op
    ((presheaf _ F (n + 1)).map (lineMap φ).op e) = 0
  rw [← Functor.map_comp_apply, ← op_comp, hv, op_comp, Functor.map_comp_apply, hU, map_zero]

end Motivic.SheafCohomology
