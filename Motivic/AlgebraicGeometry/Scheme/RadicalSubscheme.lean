/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reduced subschemes defined by radical ideal sheaves

Taking the radical of an ideal sheaf preserves its closed support and gives
an actual reduced closed subscheme. This operation discards nilpotents in the
support scheme; local multiplicities must still be measured on the original
scheme rather than on this reduction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

variable {X : Scheme.{u}}

/-- The actual closed subscheme defined by a radical ideal sheaf is reduced. -/
instance isReduced_radical_subscheme (I : X.IdealSheafData) :
    IsReduced I.radical.subscheme := by
  have hR : ∀ U : X.affineOpens, _root_.IsReduced (I.radical.subschemeCover.X U) := fun U => by
    change _root_.IsReduced (Γ(X, U) ⧸ (I.ideal U).radical)
    exact (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have hS : ∀ U : X.affineOpens,
      IsReduced (I.radical.subschemeCover.openCover.X U) := fun U => by
    change IsReduced (Spec (I.radical.subschemeCover.X U))
    have := hR U
    infer_instance
  exact @IsReduced.of_openCover I.radical.subscheme I.radical.subschemeCover.openCover hS

end Motivic
