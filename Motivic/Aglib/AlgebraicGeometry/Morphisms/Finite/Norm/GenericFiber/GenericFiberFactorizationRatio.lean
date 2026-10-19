/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PullbackRatioScalar

/-!
# Canonical generic ratios through an original factorization

An arbitrary factorization of the original generic projection transports both
line maps together. This includes the canonical global-section spectrum of a
finite affine chart. No source function field or ratio comparison is supplied.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFactorizationRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineGenericRatio`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLocalRatio`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.IdentityGenericFiberNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme

variable {C T D : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (j : D ⟶ C)
  (q : Limits.pullback f (T.fromSpecStalk (genericPoint T)) ⟶ D)
  (hq : q ≫ j = Limits.pullback.fst f (T.fromSpecStalk (genericPoint T)))
  (L : LineBundle C)

omit [IsFinite f] in
/-- Both nested original maps retain the same canonical composition comparison. -/
theorem genericFiberLineMap_factorization
    (φ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) :
    pullbackUnitMap q (pullbackUnitMap j φ) =
      ((Modules.pullbackComp q j).app L.val).hom ≫
      ((Modules.pullbackCongr hq).app L.val).hom ≫ genericFiberLineMap f L φ := by
  change _ = _ ≫ _ ≫ pullbackUnitMap _ φ
  rw [pullbackUnitMap_congr, pullbackUnitMap_comp]

include hq

/-- Invertibility of the nested denominator is derived from the actual original
monic map, rather than required as an additional factorization hypothesis. -/
theorem genericFiberLineMap_factorization_isIso
    (ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono ψ] :
    IsIso (pullbackUnitMap q (pullbackUnitMap j ψ)) := by
  rw [genericFiberLineMap_factorization f j q hq L ψ]
  let := genericFiberLineMap_isIso f L ψ
  infer_instance

/-- The original canonical generic ratio satisfies the scalar relation on every
section of the actual intermediate pullback module. -/
theorem genericFiberLineRatioUnit_mul_factorization_section
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (m : Γ((Modules.pullback j).obj L.val, ⊤)) :
    (genericFiberLineRatioUnit f L φ ψ :
        Γ(Limits.pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) *
        q.appTop (Modules.Hom.app (pullbackUnitMap j ψ) ⊤ m) =
      q.appTop (Modules.Hom.app (pullbackUnitMap j φ) ⊤ m) := by
  let := genericFiberLineMap_factorization_isIso f j q hq L ψ
  have he : inv (pullbackUnitMap q (pullbackUnitMap j ψ)) ≫
      pullbackUnitMap q (pullbackUnitMap j φ) = (genericFiberLineRatioIso f L φ ψ).hom := by
    apply (cancel_epi (pullbackUnitMap q (pullbackUnitMap j ψ))).mp
    rw [IsIso.hom_inv_id_assoc,
      genericFiberLineMap_factorization f j q hq L ψ,
      genericFiberLineMap_factorization f j q hq L φ]
    simp only [genericFiberLineRatioIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      asIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  have h := pullback_ratio_mul_section q (pullbackUnitMap j φ) (pullbackUnitMap j ψ) m
  rw [he] at h
  exact h

end AlgebraicGeometry.Scheme
