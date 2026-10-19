/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.H1.SquareDescent
public import Motivic.Transfers.Sheaf.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Lean.Util.CollectAxioms

/-!
# Standard ordinary H1 consumers for a square

The square has literal vertices `B, A, Y, X`. Its actual sheaf gluing
conditions remain explicit pending the geometric distinguished-square
constructor. These consumers retain the original transfer coefficient
universe, standard ordinary Ext and actual ordinary-injective presentation.
-/

@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.SheafCohomologyH1SquareDescent

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

/-- The original coefficient difference map corrects two actual injective lifts. -/
theorem actual_square_quotient_lift
    (sq : Square (SmoothSite (Spec (.of k))))
    (hI : (sq.op.map ((Injective.under F₀).obj ⋙
      forget AddCommGrpCat.{u + 1})).IsPullback)
    (hQ : (sq.op.map ((cokernel (Injective.ι F₀)).obj ⋙
      forget AddCommGrpCat.{u + 1})).IsPullback)
    (hsurj : Function.Surjective (fun a :
        (F₀).obj.obj (op sq.X₂) × (F₀).obj.obj (op sq.X₃) =>
      (F₀).obj.map sq.f₁₂.op a.1 - (F₀).obj.map sq.f₁₃.op a.2))
    (s : (cokernel (Injective.ι F₀)).obj.obj (op sq.X₄))
    (lA : (Injective.under F₀).obj.obj (op sq.X₂))
    (lY : (Injective.under F₀).obj.obj (op sq.X₃))
    (hA : (cokernel.π (Injective.ι F₀)).hom.app (op sq.X₂) lA =
      (cokernel (Injective.ι F₀)).obj.map sq.f₂₄.op s)
    (hY : (cokernel.π (Injective.ι F₀)).hom.app (op sq.X₃) lY =
      (cokernel (Injective.ι F₀)).obj.map sq.f₃₄.op s) :
    ∃ l : (Injective.under F₀).obj.obj (op sq.X₄),
      (cokernel.π (Injective.ι F₀)).hom.app (op sq.X₄) l = s :=
  Sheaf.exists_section_lift_of_square_difference_surjective J
    (_root_.CategoryTheory.Sheaf.LargeCohomology.injectivePresentation_shortExact.{u + 1, u, u +
        1} J F₀)
    sq hI hQ hsurj s lA lY hA hY

/-- The actual positive extension-class boundary vanishes under square descent. -/
theorem actual_square_boundary_vanishes
    {E : ShortComplex (Sheaf J AddCommGrpCat.{u + 1})} (hE : E.ShortExact)
    (sq : Square (SmoothSite (Spec (.of k))))
    (h₂ : (sq.op.map (E.X₂.obj ⋙ forget AddCommGrpCat.{u + 1})).IsPullback)
    (h₃ : (sq.op.map (E.X₃.obj ⋙ forget AddCommGrpCat.{u + 1})).IsPullback)
    (hsurj : Function.Surjective (fun a :
        E.X₁.obj.obj (op sq.X₂) × E.X₁.obj.obj (op sq.X₃) =>
      E.X₁.obj.map sq.f₁₂.op a.1 - E.X₁.obj.map sq.f₁₃.op a.2))
    (y : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1} J E.X₃ 0 sq.X₄)
    (lA : E.X₂.obj.obj (op sq.X₂)) (lY : E.X₂.obj.obj (op sq.X₃))
    (hA : E.g.hom.app (op sq.X₂) lA = E.X₃.obj.map sq.f₂₄.op
      (_root_.CategoryTheory.Sheaf.LargeCohomology.zeroSections.{u + 2, u + 1, u, u + 1} J E.X₃
        sq.X₄ y))
    (hY : E.g.hom.app (op sq.X₃) lY = E.X₃.obj.map sq.f₃₄.op
      (_root_.CategoryTheory.Sheaf.LargeCohomology.zeroSections.{u + 2, u + 1, u, u + 1} J E.X₃
        sq.X₄ y)) :
    y.comp hE.extClass rfl = 0 :=
  SheafCohomology.boundary_eq_zero_of_square_difference_surjective
    J hE sq h₂ h₃ hsurj y lA lY hA hY

/-- Square difference surjectivity kills the represented standard ordinary H1 class. -/
theorem actual_square_class_vanishes
    (sq : Square (SmoothSite (Spec (.of k))))
    (hI : (sq.op.map ((Injective.under F₀).obj ⋙
      forget AddCommGrpCat.{u + 1})).IsPullback)
    (hQ : (sq.op.map ((cokernel (Injective.ι F₀)).obj ⋙
      forget AddCommGrpCat.{u + 1})).IsPullback)
    (hsurj : Function.Surjective (fun a :
        (F₀).obj.obj (op sq.X₂) × (F₀).obj.obj (op sq.X₃) =>
      (F₀).obj.map sq.f₁₂.op a.1 - (F₀).obj.map sq.f₁₃.op a.2))
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1} J F₀ 1 sq.X₄)
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
  SheafCohomology.h_one_eq_zero_of_square_difference_surjective
    J F₀ sq hI hQ hsurj x s hs lA lY hA hY

open Lean in
run_cmd do
  for name in #[``actual_square_quotient_lift, ``actual_square_boundary_vanishes,
      ``actual_square_class_vanishes] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual H1 square descent uses only standard Lean foundations."

end MotivicTest.Cohomology.SheafCohomologyH1SquareDescent
