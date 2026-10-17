module

import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.RankOneReciprocity

/-! # Rank-one reciprocity on arbitrary open sections -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example (X : Scheme.{u}) (L : LineBundle X) (U : X.Opens)
    (d : (dualLineBundle X L).val.val.obj (op U))
    (x y : L.val.val.obj (op U)) :
    (show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) x) • y =
      (show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) y) • x :=
  dual_section_smul_exchange X L (op U) d x y

example (X : Scheme.{u}) (L : LineBundle X) (U : X.Opens)
    (d e : (dualLineBundle X L).val.val.obj (op U))
    (x y : L.val.val.obj (op U)) :
    (show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) x) *
        (show Γ(X, U) from e.val.app (op (Over.mk (𝟙 U))) y) =
      (show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) y) *
        (show Γ(X, U) from e.val.app (op (Over.mk (𝟙 U))) x) :=
  dual_section_mul_exchange X L (op U) d e x y

