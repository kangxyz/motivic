/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyH1SquareDescent
public import Motivic.Cohomology.A1.SquareDifferenceActions
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Lean.Util.CollectAxioms

/-!
# Actual endpoint splitting and its ordinary H1 consumer

The original signed cylinder correspondence gives the explicit negative
transfer right inverse. The standard ordinary H1 consumer uses this actual
splitting and the displayed geometric square gluing conditions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.A1SquareDifferenceActions

variable (k : Type u) [Field k]

local instance : IsGrothendieckAbelian.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) := by
  let : SmallCategory.{u + 1}
      (SmallModel.{u + 1, u, u + 1} (SmoothSite (Spec (.of k)))) :=
    smallCategorySmallModel.{u + 1, u, u + 1} _
  let J' : GrothendieckTopology
      (SmallModel.{u + 1, u, u + 1} (SmoothSite (Spec (.of k)))) :=
    (equivSmallModel.{u + 1, u, u + 1} (SmoothSite (Spec (.of k)))).inverse.inducedTopology
      (SmoothSite.nisnevichTopology (Spec (.of k)))
  let : HasSheafify J' AddCommGrpCat.{u + 1} := inferInstance
  exact @Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (SmoothSite (Spec (.of k))) inferInstance inferInstance
    (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}
    inferInstance inferInstance inferInstance (fun _ => inferInstance)
    (show HasSheafify J' AddCommGrpCat.{u + 1} from inferInstance)

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

variable (F : SheafWithTransfers.{u + 1} k)

local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))
local notation "F₀" => Functor.obj (SheafWithTransfers.toSheaf k) F

variable (hF : PresheafWithTransfers.IsA1Invariant F.obj)

include hF

/-- The actual transfer signs give `A` minus `Y` equal to the original section. -/
theorem actual_signed_right_inverse
    {B A Y : SmoothSite (Spec (.of k))} (p : B ⟶ A) (i : B ⟶ Y)
    (lam : Cor.mk Y ⟶ Cor.mk B) (ψ : Cor.mk A ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) B) ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 0) ≫ α = 𝟙 _)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 1) ≫ α =
      (Cor.graphFunctor k).map i ≫ lam - (Cor.graphFunctor k).map p ≫ ψ)
    (d : (F₀).obj.obj (op B)) :
    (F₀).obj.map p.op (-F.obj.transfer ψ d) -
      (F₀).obj.map i.op (-F.obj.transfer lam d) = d :=
  F.obj.restriction_difference_rightInverse_of_homotopy hF p i lam ψ α h₀ h₁ d

/-- An actual endpoint identity supplies exactly the ordinary H1 square
criterion's coefficient splitting, with the original standard Ext groups. -/
theorem actual_endpoint_split_kills_class
    (sq : Square (SmoothSite (Spec (.of k))))
    (hI : (sq.op.map ((Injective.under F₀).obj ⋙
      forget AddCommGrpCat.{u + 1})).IsPullback)
    (hQ : (sq.op.map ((cokernel (Injective.ι F₀)).obj ⋙
      forget AddCommGrpCat.{u + 1})).IsPullback)
    (lam : Cor.mk sq.X₃ ⟶ Cor.mk sq.X₁) (ψ : Cor.mk sq.X₂ ⟶ Cor.mk sq.X₁)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) sq.X₁) ⟶ Cor.mk sq.X₁)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) sq.X₁ 0) ≫ α = 𝟙 _)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) sq.X₁ 1) ≫ α =
      (Cor.graphFunctor k).map sq.f₁₃ ≫ lam - (Cor.graphFunctor k).map sq.f₁₂ ≫ ψ)
    (x : SheafCohomology.H.{u + 2, u + 1, u, u + 1} J F₀ 1 sq.X₄)
    (s : (cokernel (Injective.ι F₀)).obj.obj (op sq.X₄))
    (hs : SheafCohomology.injectiveSectionBoundary.{u + 2, u + 1, u, u + 1}
      J F₀ sq.X₄ s = x)
    (lA : (Injective.under F₀).obj.obj (op sq.X₂))
    (lY : (Injective.under F₀).obj.obj (op sq.X₃))
    (hA : (cokernel.π (Injective.ι F₀)).hom.app (op sq.X₂) lA =
      (cokernel (Injective.ι F₀)).obj.map sq.f₂₄.op s)
    (hY : (cokernel.π (Injective.ι F₀)).hom.app (op sq.X₃) lY =
      (cokernel (Injective.ι F₀)).obj.map sq.f₃₄.op s) :
    x = 0 :=
  SheafCohomology.h_one_eq_zero_of_square_difference_surjective J F₀ sq hI hQ
    (F.restriction_difference_surjective_of_homotopy hF sq.f₁₂ sq.f₁₃ lam ψ α h₀ h₁)
    x s hs lA lY hA hY

/-- A smaller-source endpoint lifts exactly the restricted original section. -/
theorem actual_shrunk_signed_difference
    {B B' A' Y' : SmoothSite (Spec (.of k))}
    (jB : B' ⟶ B) (p : B' ⟶ A') (i : B' ⟶ Y')
    (lam : Cor.mk Y' ⟶ Cor.mk B) (ψ : Cor.mk A' ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) B') ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B' 0) ≫ α =
      (Cor.graphFunctor k).map jB)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B' 1) ≫ α =
      (Cor.graphFunctor k).map i ≫ lam - (Cor.graphFunctor k).map p ≫ ψ)
    (d : (F₀).obj.obj (op B)) :
    (F₀).obj.map p.op (-F.obj.transfer ψ d) -
      (F₀).obj.map i.op (-F.obj.transfer lam d) = (F₀).obj.map jB.op d :=
  F.restriction_difference_eq_restriction_of_homotopy hF jB p i lam ψ α h₀ h₁ d

open Lean in
run_cmd do
  for name in #[``actual_signed_right_inverse, ``actual_endpoint_split_kills_class,
      ``actual_shrunk_signed_difference] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual square endpoint actions use only standard Lean foundations."

end MotivicTest.Cohomology.A1SquareDifferenceActions
