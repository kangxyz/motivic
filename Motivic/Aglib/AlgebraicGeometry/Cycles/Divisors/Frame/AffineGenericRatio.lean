/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineSectionZero
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFactorizationRatio

/-!
# The original generic ratio in canonical affine-spectrum coordinates

The frame is on the actual twofold pullback to the canonical spectrum of the
intermediate affine scheme. Composition of module pullbacks and the original
spectrum adjunction identify the scalars, without a supplied fraction relation.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineGenericRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioChartCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme

/-- Evaluation in the same canonical affine frame gives the literal scalar
numerator/denominator relation for the original global generic ratio. -/
theorem genericFiberLineRatioUnit_mul_affineFrame
    {C T D : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
    [IsAffine D] (j : D ⟶ C)
    (q : Limits.pullback f (T.fromSpecStalk (genericPoint T)) ⟶ D)
    (hq : q ≫ j = Limits.pullback.fst f (T.fromSpecStalk (genericPoint T)))
    (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (e : (pullbackLineBundle D.isoSpec.inv (pullbackLineBundle j L)).val.over ⊤ ≅
      SheafOfModules.unit ((Spec Γ(D, ⊤)).ringCatSheaf.over ⊤)) :
    (Scheme.genericFiberLineRatioUnit f L φ ψ :
        Γ(Limits.pullback f (T.fromSpecStalk (genericPoint T)), ⊤)) *
        q.appTop (affineFrameScalar Γ(D, ⊤)
          (pullbackLineBundle D.isoSpec.inv (pullbackLineBundle j L))
          (pullbackUnitMap D.isoSpec.inv (pullbackUnitMap j ψ)) e) =
      q.appTop (affineFrameScalar Γ(D, ⊤)
        (pullbackLineBundle D.isoSpec.inv (pullbackLineBundle j L))
        (pullbackUnitMap D.isoSpec.inv (pullbackUnitMap j φ)) e) := by
  let m := chartGenerator (Spec Γ(D, ⊤))
    (pullbackLineBundle D.isoSpec.inv (pullbackLineBundle j L)).val ⊤ e
  let E := (Scheme.Modules.pullbackComp D.isoSpec.inv j).app L.val
  let m' := Scheme.Modules.Hom.app E.hom ⊤ m
  have hq' : (q ≫ D.isoSpec.hom) ≫ (D.isoSpec.inv ≫ j) =
      Limits.pullback.fst f (T.fromSpecStalk (genericPoint T)) := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hq
  have h := Scheme.genericFiberLineRatioUnit_mul_factorization_section f
    (D.isoSpec.inv ≫ j) (q ≫ D.isoSpec.hom) hq' L φ ψ m'
  have happ (θ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) :
      Scheme.Modules.Hom.app (pullbackUnitMap (D.isoSpec.inv ≫ j) θ) ⊤ m' =
        Scheme.Modules.Hom.app (pullbackUnitMap D.isoSpec.inv (pullbackUnitMap j θ)) ⊤ m := by
    exact congrArg (fun k => Scheme.Modules.Hom.app k ⊤ m)
      (pullbackUnitMap_comp D.isoSpec.inv j θ)
  rw [happ ψ, happ φ] at h
  have hΓ : D.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(D, ⊤)).hom :=
    Scheme.toSpecΓ_appTop D
  simp only [Scheme.Hom.comp_appTop, hΓ, CommRingCat.comp_apply] at h
  simp only [affineFrameScalar]
  dsimp only [m] at h
  convert h using 1

end AlgebraicGeometry.Scheme
