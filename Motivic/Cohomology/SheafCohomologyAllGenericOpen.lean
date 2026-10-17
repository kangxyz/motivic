/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyArtinianNeighborhoodLift
public import Motivic.Aglib.AlgebraicGeometry.SheafGenericOpenSectionLift
public import Motivic.AlgebraicGeometry.SmoothSiteInjectives

/-! # Positive ordinary classes vanish on an open containing every generic point -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every positive ordinary class vanishes on an actual open containing all generic points.
No separatedness of the higher-cohomology presheaf is used. -/
theorem exists_all_generic_open_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite (Spec (.of k)))
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 1) X) :
    ∃ O : X.left.Opens, genericPoints X.left ⊆ (O : Set X.left) ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 1)).map (SmoothSite.openInclusion X O).op e = 0 := by
  let J := SmoothSite.nisnevichTopology (Spec (.of k))
  induction n generalizing F with
  | zero =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (Hypercohomology.freeAbelianSheaf J X) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨O, hO, l, hl⟩ := SmoothSite.exists_all_generic_open_section_lift E.g X
      (zeroSections.{w, u + 1, u, u + 1} J E.X₃ X y)
    refine ⟨O, hO, ?_⟩
    rw [← hy]
    exact boundary_restriction_eq_zero_of_imageSieve.{w, u + 1, u, u + 1} J hE y
      (SmoothSite.openInclusion X O) ⟨l, hl⟩
  | succ n ih =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (Hypercohomology.freeAbelianSheaf J X) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨O, hO, hz⟩ := ih E.X₃ y
    let p := SmoothSite.openInclusion X O
    let Y := (SmoothSite.opensFunctor X).obj O
    refine ⟨O, hO, ?_⟩
    rw [← hy]
    change (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map p)).comp
      (y.comp hE.extClass rfl) (zero_add (n + 1 + 1)) = 0
    rw [← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega)]
    change ((presheaf.{w, u + 1, u, u + 1} J E.X₃ (n + 1)).map p.op y).comp hE.extClass rfl = 0
    rw [hz]
    exact Ext.zero_comp (Hypercohomology.freeAbelianSheaf J Y) (n + 1) hE.extClass _ rfl

end Motivic.SheafCohomology
