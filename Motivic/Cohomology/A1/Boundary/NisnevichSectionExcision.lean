/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
/-! # Relations in actual punctured-section quotients reflect across Nisnevich neighborhoods

This is injectivity, not surjectivity, of the original section-cokernel map.
It uses genuine sheaf descent and does not assume homotopy invariance.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe v u
private theorem sectionCokernel_mono {A B C D : AddCommGrpCat.{v}}
    (f : A ⟶ B) (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : f ≫ b = a ≫ g) (H : IsPullback f a b g) :
    Mono (cokernel.map f g a b w) :=
  Abelian.mono_cokernel_map_of_isPullback H

namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} (sq : Square (SmoothSite S))
  (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{v})

/-- The literal restriction map between the original punctured-section cokernels. -/
def sectionQuotientRestriction :
    cokernel (F.obj.map sq.f₂₄.op) ⟶ cokernel (F.obj.map sq.f₁₃.op) :=
  cokernel.map _ _ (F.obj.map sq.f₃₄.op) (F.obj.map sq.f₁₂.op) (sq.op.map F.obj).fac

@[reassoc (attr := simp)]
theorem sectionQuotientRestriction_π :
    cokernel.π (F.obj.map sq.f₂₄.op) ≫ sectionQuotientRestriction sq F =
      F.obj.map sq.f₁₂.op ≫ cokernel.π (F.obj.map sq.f₁₃.op) :=
  cokernel.π_desc _ _ _

variable (hpb : sq.IsPullback) [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

include hpb z hcomp in
/-- Actual Nisnevich neighborhood restriction is injective on section quotients. -/
theorem sectionQuotientRestriction_mono : Mono (sectionQuotientRestriction sq F) := by
  have H : IsPullback (F.obj.map sq.f₂₄.op) (F.obj.map sq.f₃₄.op)
      (F.obj.map sq.f₁₂.op) (F.obj.map sq.f₁₃.op) :=
    isPullback_op_map_of_iso_complement sq hpb z hcomp F
  unfold sectionQuotientRestriction
  exact sectionCokernel_mono _ _ _ _ _ H

include hpb z hcomp in
/-- A relation detected on a genuine Nisnevich neighborhood already holds originally.
Both the punctured section and its neighborhood extension are retained literally. -/
theorem exists_section_extension_of_neighborhood
    (a : F.obj.obj (op sq.X₂)) (c : F.obj.obj (op sq.X₃))
    (h : F.obj.map sq.f₁₂.op a = F.obj.map sq.f₁₃.op c) :
    ∃ b : F.obj.obj (op sq.X₄),
      F.obj.map sq.f₂₄.op b = a ∧ F.obj.map sq.f₃₄.op b = c := by
  have H := (CategoryTheory.forget AddCommGrpCat.{v}).map_isPullback
    (isPullback_op_map_of_iso_complement sq hpb z hcomp F)
  exact Types.exists_of_isPullback H a c h
end AlgebraicGeometry.Scheme.SmoothSite
