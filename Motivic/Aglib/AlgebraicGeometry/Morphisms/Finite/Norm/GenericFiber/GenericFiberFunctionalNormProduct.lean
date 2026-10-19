/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFunctionalRatio

/-! # The actual local E5 product and its native rational germ

Both quotients are formed from the same original functionals. The source norm
uses the whole finite chart and its original scalar action. Only the target is
integral. No local scalar normalization or germ-equality family is supplied.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFunctionalNormProduct`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- The product of the original target quotient and the correction norm is a
unit on every actual common functional-unit chart and has the canonical product germ. -/
theorem genericFiberFunctionalNormProduct_unit_and_germ
    {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
    (N : LineBundle C) (n d : N.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [Mono n] [Mono d]
    (L : LineBundle T) (a c : L.val ⟶ SheafOfModules.unit T.ringCatSheaf)
    [Mono a] [Mono c]
    (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIso (pullbackUnitMap U.ι a)] [IsIso (pullbackUnitMap U.ι c)]
    [IsIso (pullbackUnitMap (pullback.fst f hU.fromSpec) n)]
    [IsIso (pullbackUnitMap (pullback.fst f hU.fromSpec) d)] :
    let b : Γ(pullback f hU.fromSpec, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap (pullback.fst f hU.fromSpec) d) ≫
        pullbackUnitMap (pullback.fst f hU.fromSpec) n) ⊤
          (1 : Γ(pullback f hU.fromSpec, ⊤))
    let a₀ : Γ(U.toScheme, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap U.ι c) ≫ pullbackUnitMap U.ι a) ⊤ (1 : Γ(U.toScheme, ⊤))
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      IsUnit (U.topIso.hom a₀ * Algebra.norm Γ(T, U) b) ∧
      T.germToFunctionField U (U.topIso.hom a₀ * Algebra.norm Γ(T, U) b) =
        genericFiberLineRatioNorm (𝟙 T) L a c * genericFiberLineRatioNorm f N n d := by
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  constructor
  · apply IsUnit.mul
    · exact (Modules.isUnit_unitEnd_app_one U.toScheme _).map U.topIso.hom.hom
    · exact (Modules.isUnit_unitEnd_app_one (pullback f hU.fromSpec) _).map
        (Algebra.norm Γ(T, U))
  · rw [map_mul, ← genericFiberLineRatioNorm_id_eq_functionalQuotient_germ L a c U,
      ← genericFiberLineRatioNorm_eq_chart_functionalQuotient f N n d U hU]

end AlgebraicGeometry.Scheme
