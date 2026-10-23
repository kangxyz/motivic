/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Relative.Naturality
public import Motivic.Aglib.CategoryTheory.Sites.FreeAbelianSheafPushout
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Relative excision for ordinary sheaf cohomology
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe w t v u
namespace CategoryTheory.Sheaf.LargeCohomology
section General

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  (sq : Square C)

/-- Section descent identifies the actual relative cokernel map. -/
theorem isIso_relativeSourceMap_of_section_descent
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback) :
    IsIso (relativeSourceMap J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm) := by
  exact isIso_cokernel_map_of_isPushout
    (Hypercohomology.freeAbelianSheaf_isPushout J sq h).flip

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- The existing relative restriction is an isomorphism in every Ext degree. -/
theorem isIso_relativeRestriction_of_section_descent
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback)
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    IsIso (relativeRestriction J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F n) := by
  let := isIso_relativeSourceMap_of_section_descent J sq h
  change IsIso (((extFunctor n).map
    (relativeSourceMap J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm).op).app F)
  infer_instance

end General

end CategoryTheory.Sheaf.LargeCohomology
