/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.ArtinianNeighborhoodLift
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Injectives

/-! # Killing positive ordinary classes near the entire Artinian closed subscheme -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open _root_.CategoryTheory.Sheaf
open _root_.CategoryTheory.Sheaf.LargeCohomology
variable {S : Scheme.{u}} [IsNoetherian S]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- Every positive ordinary class vanishes on a constructed étale neighborhood
of the full Artinian closed subscheme. Ordinary injective cokernels are used
only for dimension shifting; no homotopy invariance is claimed for them. -/
theorem exists_etale_neighborhood_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite S)
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F (n + 1) X)
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z] [IsLocallyArtinian Z] :
    ∃ (Y : SmoothSite S) (p : Y ⟶ X), Etale p.left ∧
      IsIso (pullback.snd p.left z) ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S)
        F (n + 1)).map p.op e = 0 := by
  let J := SmoothSite.nisnevichTopology S
  induction n generalizing F with
  | zero =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (Hypercohomology.freeAbelianSheaf J X) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨Y, p, hp, hZ, l, hl⟩ := exists_etale_neighborhood_lift E.g X
      (zeroSections.{w, u + 1, u, u + 1} J E.X₃ X y) z
    refine ⟨Y, p, hp, hZ, ?_⟩
    rw [← hy]
    exact boundary_restriction_eq_zero_of_imageSieve.{w, u + 1, u, u + 1} J hE y p ⟨l, hl⟩
  | succ n ih =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (Hypercohomology.freeAbelianSheaf J X) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨Y, p, hp, hZ, hz⟩ := ih E.X₃ y
    refine ⟨Y, p, hp, hZ, ?_⟩
    rw [← hy]
    change (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map p)).comp
      (y.comp hE.extClass rfl) (zero_add (n + 1 + 1)) = 0
    rw [← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega)]
    change ((presheaf.{w, u + 1, u, u + 1} J E.X₃ (n + 1)).map p.op y).comp hE.extClass rfl = 0
    rw [hz]
    exact Ext.zero_comp (Hypercohomology.freeAbelianSheaf J Y) (n + 1) hE.extClass _ rfl

end Motivic.SheafCohomology
