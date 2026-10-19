/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio

/-! # Inversion of the canonical original-map generic ratio

Only the whole generic fiber is used. Neither local invertibility of a graph
coefficient nor a function field of the possibly disconnected source is required.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatioInverse`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme

variable {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (L : LineBundle C)
  (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]

/-- Swapping the same original numerator and denominator inverts their actual
generic-fiber unit. No local frame or local section unit is supplied. -/
theorem genericFiberLineRatioUnit_swap :
    genericFiberLineRatioUnit f L ψ φ = (genericFiberLineRatioUnit f L φ ψ)⁻¹ := by
  apply Units.ext
  rfl

/-- The determinant norm of the swapped original ratio is the inverse norm.
This uses the actual norm on the whole finite generic fiber. -/
theorem genericFiberLineRatioNorm_swap :
    genericFiberLineRatioNorm f L ψ φ = (genericFiberLineRatioNorm f L φ ψ)⁻¹ := by
  let K := T.functionField
  let G := pullback f (T.fromSpecStalk (genericPoint T))
  let q := pullback.snd f (T.fromSpecStalk (genericPoint T))
  let : Algebra K Γ(G, ⊤) := (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
  let : Module.Finite K Γ(G, ⊤) := FiniteSchemeNormBaseChange.sections_finite q
  change Algebra.norm K (genericFiberLineRatioUnit f L ψ φ).val =
    (Algebra.norm K (genericFiberLineRatioUnit f L φ ψ).val)⁻¹
  rw [genericFiberLineRatioUnit_swap]
  let h := genericFiberLineRatioUnit f L φ ψ
  calc
    Algebra.norm K (h⁻¹).val = (Units.map (Algebra.norm K) (h⁻¹)).val := rfl
    _ = ((Units.map (Algebra.norm K) h)⁻¹).val :=
      congrArg Units.val (map_inv (Units.map (Algebra.norm K)) h)
    _ = (Algebra.norm K h.val)⁻¹ := Units.val_inv_eq_inv_val _

end AlgebraicGeometry.Scheme
