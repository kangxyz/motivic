/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PullbackRatioScalar

/-!
# Original section coordinates of the canonical generic line ratio

The original two maps and original global section determine the multiplication
identity on the whole actual generic fiber. A shared frame is used only by
choosing its original generator as that section, not in defining the ratio.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatioScalar`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme

/-- The canonical generic ratio satisfies the actual numerator/denominator
relation on every original section, without a supplied ratio comparison. -/
theorem genericFiberLineRatioUnit_mul_section
    {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
    (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (m : Γ((show C.Modules from L.val), ⊤)) :
    (genericFiberLineRatioUnit f L φ ψ :
        Γ(CategoryTheory.Limits.pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) *
        (Limits.pullback.fst f (T.fromSpecStalk (genericPoint T))).appTop
          (Modules.Hom.app ψ ⊤ m) =
      (Limits.pullback.fst f (T.fromSpecStalk (genericPoint T))).appTop
        (Modules.Hom.app φ ⊤ m) := by
  let q := Limits.pullback.fst f (T.fromSpecStalk (genericPoint T))
  let : IsIso (Modules.Invertible.pullbackUnitMap q ψ) :=
    genericFiberLineMap_isIso f L ψ
  exact Modules.Invertible.pullback_ratio_mul_section q φ ψ m

end AlgebraicGeometry.Scheme
