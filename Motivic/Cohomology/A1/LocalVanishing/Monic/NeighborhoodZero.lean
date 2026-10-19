/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Monic.NeighborhoodLift
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Injectives
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.LocalTriviality

/-! # Killing positive ordinary classes near the entire relative monic divisor -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open _root_.CategoryTheory.Sheaf
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Algebra.Smooth _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- Every positive original ordinary cohomology class vanishes on an affine
étale neighborhood of the full monic divisor after one nonzero base localization. -/
theorem exists_relative_monic_neighborhood_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (f : R[X]) (hf : f.Monic)
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k))) F (n + 1)
      (lineSite (k := k) (R := R))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (Y : SmoothSite (Spec (.of k)))
      (p : Y ⟶ lineSite (k := k) (R := Localization.Away r)),
      IsAffine Y.left ∧ Etale p.left ∧
      IsIso (pullback.snd p.left (inclusion (f.map (algebraMap R (Localization.Away r))))) ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 1)).map
          (p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e = 0 := by
  let X := lineSite (k := k) (R := R)
  let J := SmoothSite.nisnevichTopology (Spec (.of k))
  induction n generalizing F with
  | zero =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (Hypercohomology.freeAbelianSheaf J X) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨r, hr, Y, p, hY, hp, hZ, l, hl⟩ := exists_relative_monic_neighborhood_lift E.g f hf
      (zeroSections.{w, u + 1, u, u + 1} J E.X₃ X y)
    refine ⟨r, hr, Y, p, hY, hp, hZ, ?_⟩
    rw [← hy]
    exact boundary_restriction_eq_zero_of_imageSieve.{w, u + 1, u, u + 1} J hE y _ ⟨l, hl⟩
  | succ n ih =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (Hypercohomology.freeAbelianSheaf J X) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨r, hr, Y, p, hY, hp, hZ, hz⟩ := ih E.X₃ y
    let a := p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))
    refine ⟨r, hr, Y, p, hY, hp, hZ, ?_⟩
    rw [← hy]
    change (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map a)).comp
      (y.comp hE.extClass rfl) (zero_add (n + 1 + 1)) = 0
    rw [← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega)]
    change ((presheaf.{w, u + 1, u, u + 1} J E.X₃ (n + 1)).map a.op y).comp hE.extClass rfl = 0
    rw [hz]
    exact Ext.zero_comp (Hypercohomology.freeAbelianSheaf J Y) (n + 1) hE.extClass _ rfl

end Motivic.SheafCohomology
