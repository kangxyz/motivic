/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLocalRatio

/-! # Native norm germs of actual functional-unit quotients

These quotients use the literal pulled functionals, including noncanonical
pulled evaluation pairings. No identification with a newly chosen dual is made.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFunctionalRatio`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.`
Module suffix: `GenericFiberFunctionalNormProduct`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar of an actual structure-module automorphism is a unit. -/
theorem isUnit_unitEnd_app_one (X : Scheme.{u})
    (θ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso θ] : IsUnit (show Γ(X, ⊤) from Hom.app θ ⊤ (1 : Γ(X, ⊤))) := by
  refine ⟨⟨Hom.app θ ⊤ (1 : Γ(X, ⊤)),
    Hom.app (inv θ) ⊤ (1 : Γ(X, ⊤)), ?_, ?_⟩, rfl⟩
  · apply unitMul_injective X
    rw [unitMul_mul, ← unitEnd_eq_unitMul X θ,
      ← unitEnd_eq_unitMul X (inv θ), IsIso.hom_inv_id, unitMul_one]
  · apply unitMul_injective X
    rw [unitMul_mul, ← unitEnd_eq_unitMul X (inv θ),
      ← unitEnd_eq_unitMul X θ, IsIso.inv_hom_id, unitMul_one]

end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme

variable {C T W : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (j : W ⟶ C) (q : pullback f (T.fromSpecStalk (genericPoint T)) ⟶ W)
  (hq : q ≫ j = pullback.fst f (T.fromSpecStalk (genericPoint T)))
  (L : LineBundle C)
  (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]

include hq in
/-- Invert the actual local denominator functional, not a newly canonicalized
section functional. Its generic restriction is the original canonical ratio. -/
theorem genericFiberLineRatioUnit_eq_functionalQuotient
    [IsIso (pullbackUnitMap j ψ)] :
    (genericFiberLineRatioUnit f L φ ψ :
      Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) =
    q.appTop (Modules.Hom.app
      (inv (pullbackUnitMap j ψ) ≫ pullbackUnitMap j φ) ⊤ (1 : Γ(W, ⊤))) := by
  have he := genericFiberLineRatioIso_eq_pullback_of_equation f j q hq L φ ψ
    (inv (pullbackUnitMap j ψ) ≫ pullbackUnitMap j φ) (by
      rw [IsIso.hom_inv_id_assoc])
  change Modules.Hom.app (genericFiberLineRatioIso f L φ ψ).hom ⊤
    (1 : Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) = _
  rw [he]
  exact Hom.unitEndomorphismPullback_app_one q _

omit j q hq in
/-- The local norm of the original functional quotient has the canonical native
target germ. Original total-chart freeness is the only module-freeness premise. -/
theorem genericFiberLineRatioNorm_eq_chart_functionalQuotient
    (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIso (pullbackUnitMap (pullback.fst f hU.fromSpec) ψ)] :
    let b : Γ(pullback f hU.fromSpec, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap (pullback.fst f hU.fromSpec) ψ) ≫
        pullbackUnitMap (pullback.fst f hU.fromSpec) φ) ⊤
          (1 : Γ(pullback f hU.fromSpec, ⊤))
    let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback f hU.fromSpec, ⊤)],
      genericFiberLineRatioNorm f L φ ψ =
        T.germToFunctionField U (Algebra.norm Γ(T, U) b) := by
  let : Algebra Γ(T, U) Γ(pullback f hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  change Algebra.norm T.functionField (genericFiberLineRatioUnit f L φ ψ :
    Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) = _
  rw [genericFiberLineRatioUnit_eq_functionalQuotient f (pullback.fst f hU.fromSpec)
    (genericFiberChartProjection f U hU) (genericFiberChartProjection_fst f U hU) L φ ψ]
  exact norm_genericFiberChartProjection f U hU _

/-- The identity-target functional quotient has the original identity norm as
native germ, retaining the literal pulled numerator and denominator maps. -/
theorem genericFiberLineRatioNorm_id_eq_functionalQuotient_germ
    {X : Scheme.{u}} [IsIntegral X] (M : LineBundle X)
    (a c : M.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono a] [Mono c]
    (U : X.Opens) [Nonempty U] [IsIso (pullbackUnitMap U.ι c)] :
    let b : Γ(U.toScheme, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap U.ι c) ≫ pullbackUnitMap U.ι a) ⊤ (1 : Γ(U.toScheme, ⊤))
    genericFiberLineRatioNorm (𝟙 X) M a c = X.germToFunctionField U (U.topIso.hom b) := by
  dsimp only
  apply genericFiberLineRatioNorm_id_eq_germ M a c U
  rw [Iso.hom_inv_id_apply, ← Modules.unitEnd_eq_unitMul, IsIso.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme
