/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.Sheaf.H1.NisnevichSquareDescent
public import Motivic.Cohomology.A1.LocalVanishing.RelativeCurve.LocalLifting

/-! # Correcting an original H¹ discrepancy after base restriction -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open _root_.CategoryTheory.Sheaf
open _root_.CategoryTheory.Sheaf.LargeCohomology
variable {S : Scheme.{u}}
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- Naturality for the actual ordinary injective-cokernel boundary. -/
theorem injectiveSectionBoundary_restriction
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    {X Y : SmoothSite S} (f : Y ⟶ X)
    (s : (cokernel (Injective.ι F)).obj.obj (op X)) :
    injectiveSectionBoundary.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F Y
      ((cokernel (Injective.ι F)).obj.map f.op s) =
    (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1).map f.op
      (injectiveSectionBoundary.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F X s) := by
  let J := SmoothSite.nisnevichTopology S
  let Q := cokernel (Injective.ι F)
  have h : (zeroSections.{w, u + 1, u, u + 1} J Q Y).symm (Q.obj.map f.op s) =
      (presheaf.{w, u + 1, u, u + 1} J Q 0).map f.op
        ((zeroSections.{w, u + 1, u, u + 1} J Q X).symm s) := by
    apply (zeroSections.{w, u + 1, u, u + 1} J Q Y).injective
    rw [AddEquiv.apply_symm_apply, zeroSections_restriction, AddEquiv.apply_symm_apply]
  rw [injectiveSectionBoundary_apply, injectiveSectionBoundary_apply, h]
  change ((Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map f)).comp
    ((zeroSections.{w, u + 1, u, u + 1} J Q X).symm s) (zero_add 0)).comp
      (injectivePresentation_shortExact.{u + 1, u, u + 1} J F).extClass rfl = _
  rw [Ext.comp_assoc_of_second_deg_zero]
  rfl

/-- A vanishing restriction of H¹ produces a lift of the same original quotient
section. This is exactness of Ext, not a sheaf assertion for H¹. -/
theorem exists_injective_lift_of_boundary_restriction_zero
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    {X Y : SmoothSite S} (f : Y ⟶ X)
    (s : (cokernel (Injective.ι F)).obj.obj (op X))
    (h : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1).map f.op
      (injectiveSectionBoundary.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F X s) = 0) :
    ∃ l : (Injective.under F).obj.obj (op Y),
      (cokernel.π (Injective.ι F)).hom.app (op Y) l =
        (cokernel (Injective.ι F)).obj.map f.op s := by
  let J := SmoothSite.nisnevichTopology S
  let E := injectivePresentation.{u + 1, u, u + 1} J F
  have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
  rw [← injectiveSectionBoundary_restriction, injectiveSectionBoundary_apply] at h
  obtain ⟨l, hl⟩ := Ext.covariant_sequence_exact₃
    (Hypercohomology.freeAbelianSheaf J Y) hE _ rfl h
  refine ⟨zeroSections.{w, u + 1, u, u + 1} J E.X₂ Y l, ?_⟩
  have hh := congrArg (zeroSections.{w, u + 1, u, u + 1} J E.X₃ Y) hl
  change zeroSections.{w, u + 1, u, u + 1} J E.X₃ Y
    (((presheafFunctor.{w, u + 1, u, u + 1} J 0).map E.g).app (op Y) l) = _ at hh
  rw [zeroSections_naturality] at hh
  exact hh.trans ((zeroSections.{w, u + 1, u, u + 1} J E.X₃ Y).apply_symm_apply _)

/-- Restriction of the original discrepancy suffices on the new Nisnevich square.
All four displayed maps are retained, so a base-only restriction cannot silently
be replaced by shrinking the affine-line parameter. -/
theorem h_one_restriction_eq_zero_of_square_difference_lifting
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (sq sq' : Square (SmoothSite S)) (hpb : sq'.IsPullback)
    (j₁ : sq'.X₁ ⟶ sq.X₁) (j₂ : sq'.X₂ ⟶ sq.X₂)
    (j₃ : sq'.X₃ ⟶ sq.X₃) (j₄ : sq'.X₄ ⟶ sq.X₄)
    (h₁₂ : j₁ ≫ sq.f₁₂ = sq'.f₁₂ ≫ j₂)
    (h₁₃ : j₁ ≫ sq.f₁₃ = sq'.f₁₃ ≫ j₃)
    (h₂₄ : j₂ ≫ sq.f₂₄ = sq'.f₂₄ ≫ j₄)
    (h₃₄ : j₃ ≫ sq.f₃₄ = sq'.f₃₄ ≫ j₄)
    [IsOpenImmersion sq'.f₂₄.left] [Etale sq'.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq'.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq'.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq'.f₃₄.left z)]
    (hL : ∀ d : F.obj.obj (op sq.X₁),
      ∃ a : F.obj.obj (op sq'.X₂), ∃ b : F.obj.obj (op sq'.X₃),
        F.obj.map sq'.f₁₂.op a - F.obj.map sq'.f₁₃.op b = F.obj.map j₁.op d)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1 sq.X₄)
    (hA : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1).map
      sq.f₂₄.op x = 0)
    (hY : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1).map
      sq.f₃₄.op x = 0) :
    (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F 1).map j₄.op x = 0 := by
  let J := SmoothSite.nisnevichTopology S
  let I := Injective.under F
  let Q := cokernel (Injective.ι F)
  obtain ⟨s, hs⟩ := injectiveSectionBoundary_surjective.{w, u + 1, u, u + 1} J F sq.X₄ x
  obtain ⟨lA, hlA⟩ := exists_injective_lift_of_boundary_restriction_zero.{w, u} F sq.f₂₄ s
    (by rw [show injectiveSectionBoundary.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology S) F sq.X₄ s = x from hs]; exact hA)
  obtain ⟨lY, hlY⟩ := exists_injective_lift_of_boundary_restriction_zero.{w, u} F sq.f₃₄ s
    (by rw [show injectiveSectionBoundary.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology S) F sq.X₄ s = x from hs]; exact hY)
  obtain ⟨d, hd, _⟩ := Sheaf.existsUnique_localLiftDifference J
    (injectivePresentation_shortExact.{u + 1, u, u + 1} J F)
    sq.f₂₄ sq.f₃₄ sq.f₁₂ sq.f₁₃ sq.fac
    s lA lY hlA hlY
  change (Injective.ι F).hom.app (op sq.X₁) d =
    I.obj.map sq.f₁₂.op lA - I.obj.map sq.f₁₃.op lY at hd
  obtain ⟨a, b, hab⟩ := hL d
  refine h_one_eq_zero_of_nisnevich_square_correction F sq' hpb z hcomp
    _ (Q.obj.map j₄.op s) (by rw [injectiveSectionBoundary_restriction, hs])
    (I.obj.map j₂.op lA) (I.obj.map j₃.op lY) ?_ ?_ a b ?_
  · rw [(cokernel.π (Injective.ι F)).hom.naturality_apply, hlA,
      ← Functor.map_comp_apply, ← op_comp, h₂₄, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply]
  · rw [(cokernel.π (Injective.ι F)).hom.naturality_apply, hlY,
      ← Functor.map_comp_apply, ← op_comp, h₃₄, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply]
  · rw [hab, (Injective.ι F).hom.naturality_apply, hd, map_sub]
    change I.obj.map sq'.f₁₂.op (I.obj.map j₂.op lA) -
      I.obj.map sq'.f₁₃.op (I.obj.map j₃.op lY) =
      I.obj.map j₁.op (I.obj.map sq.f₁₂.op lA) -
        I.obj.map j₁.op (I.obj.map sq.f₁₃.op lY)
    simp only [← Functor.map_comp_apply, ← op_comp, h₁₂, h₁₃]

end Motivic.SheafCohomology
