/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.AbelianCechDescent
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Lifting quotient sections on a square

For a square with vertices `B, A, Y, X`, suppose the middle and quotient
sheaves satisfy the actual square gluing condition. Surjectivity of the
kernel-sheaf difference map `F(A) × F(Y) → F(B)` then allows local lifts
over `A` and `Y` to be corrected and glued over `X`.

The square gluing conditions are explicit geometric inputs. In particular,
they impose no restriction relating the coefficient and site universes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits Opposite

universe t v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{t}]

/-- Surjectivity of the literal kernel-section difference map permits two
local quotient lifts to be corrected and glued on an actual square. -/
theorem exists_section_lift_of_square_difference_surjective
    {E : ShortComplex (Sheaf J AddCommGrpCat.{t})} (hE : E.ShortExact)
    (sq : Square C)
    (h₂ : (sq.op.map (E.X₂.obj ⋙ forget AddCommGrpCat.{t})).IsPullback)
    (h₃ : (sq.op.map (E.X₃.obj ⋙ forget AddCommGrpCat.{t})).IsPullback)
    (hsurj : Function.Surjective (fun a :
        E.X₁.obj.obj (op sq.X₂) × E.X₁.obj.obj (op sq.X₃) =>
      E.X₁.obj.map sq.f₁₂.op a.1 - E.X₁.obj.map sq.f₁₃.op a.2))
    (s : E.X₃.obj.obj (op sq.X₄))
    (lA : E.X₂.obj.obj (op sq.X₂)) (lY : E.X₂.obj.obj (op sq.X₃))
    (hA : E.g.hom.app (op sq.X₂) lA = E.X₃.obj.map sq.f₂₄.op s)
    (hY : E.g.hom.app (op sq.X₃) lY = E.X₃.obj.map sq.f₃₄.op s) :
    ∃ l : E.X₂.obj.obj (op sq.X₄), E.g.hom.app (op sq.X₄) l = s := by
  obtain ⟨d, hd, _⟩ := existsUnique_localLiftDifference J hE
    sq.f₂₄ sq.f₃₄ sq.f₁₂ sq.f₁₃ sq.fac s lA lY hA hY
  obtain ⟨⟨aA, aY⟩, ha⟩ := hsurj d
  have hcompat :
      E.X₂.obj.map sq.f₁₂.op (lA - E.f.hom.app (op sq.X₂) aA) =
        E.X₂.obj.map sq.f₁₃.op (lY - E.f.hom.app (op sq.X₃) aY) := by
    rw [map_sub, map_sub, ← E.f.hom.naturality_apply sq.f₁₂.op aA,
      ← E.f.hom.naturality_apply sq.f₁₃.op aY]
    have h := hd.symm.trans (congrArg (E.f.hom.app (op sq.X₁)) ha.symm)
    rw [map_sub] at h
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  obtain ⟨l, hlA, hlY⟩ := Types.exists_of_isPullback h₂
    (lA - E.f.hom.app (op sq.X₂) aA) (lY - E.f.hom.app (op sq.X₃) aY) hcompat
  change E.X₂.obj.map sq.f₂₄.op l = _ at hlA
  change E.X₂.obj.map sq.f₃₄.op l = _ at hlY
  have hzero (Z : C) (a : E.X₁.obj.obj (op Z)) :
      E.g.hom.app (op Z) (E.f.hom.app (op Z) a) = 0 := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun η => η.hom.app (op Z)) E.zero) a
  refine ⟨l, Types.ext_of_isPullback h₃ ?_ ?_⟩
  · change E.X₃.obj.map sq.f₂₄.op (E.g.hom.app (op sq.X₄) l) =
      E.X₃.obj.map sq.f₂₄.op s
    rw [← E.g.hom.naturality_apply sq.f₂₄.op l, hlA, map_sub, hA, hzero, sub_zero]
  · change E.X₃.obj.map sq.f₃₄.op (E.g.hom.app (op sq.X₄) l) =
      E.X₃.obj.map sq.f₃₄.op s
    rw [← E.g.hom.naturality_apply sq.f₃₄.op l, hlY, map_sub, hY, hzero, sub_zero]

end CategoryTheory.Sheaf
