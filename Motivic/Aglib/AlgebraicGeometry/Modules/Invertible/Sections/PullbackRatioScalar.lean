/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General

/-!
# The actual pulled-back ratio evaluated in original section coordinates

The denominator is inverted only after its actual pullback is an isomorphism.
The scalar relation retains the original section and the original scheme map;
no source function field or independently supplied ratio equality is used.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PullbackRatioScalar`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartFrameNorm`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFactorizationRatio`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatioScalar`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The canonical ratio of two pulled-back maps multiplies the actual pulled
original denominator coordinate to the actual numerator coordinate. -/
theorem pullback_ratio_mul_section {X Y : Scheme.{u}} (q : Y ⟶ X)
    {M : X.Modules}
    (φ ψ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    [IsIso (pullbackUnitMap q ψ)] (m : Γ(M, ⊤)) :
    (show Γ(Y, ⊤) from Scheme.Modules.Hom.app
        (inv (pullbackUnitMap q ψ) ≫ pullbackUnitMap q φ) ⊤ (1 : Γ(Y, ⊤))) *
        q.appTop (Scheme.Modules.Hom.app ψ ⊤ m) =
      q.appTop (Scheme.Modules.Hom.app φ ⊤ m) := by
  let t : (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) :=
    inv (pullbackUnitMap q ψ) ≫ pullbackUnitMap q φ
  let adj := Modules.pullbackPushforwardAdjunction q
  have hφ : adj.homEquiv _ _ (pullbackUnitMap q φ) =
      φ ≫ SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
    rw [pullbackUnitMap, adj.homEquiv_naturality_left, pullbackUnitIso_homEquiv]
  have hψ : adj.homEquiv _ _ (pullbackUnitMap q ψ) =
      ψ ≫ SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
    rw [pullbackUnitMap, adj.homEquiv_naturality_left, pullbackUnitIso_homEquiv]
  have h : (ψ ≫ SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom) ≫
      (Modules.pushforward q).map t =
      φ ≫ SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
    rw [← hψ, ← adj.homEquiv_naturality_right]
    simpa [t] using hφ
  have hs := congrArg (fun k => Scheme.Modules.Hom.app k ⊤ m) h
  change Scheme.Modules.Hom.app t ⊤ (q.appTop (Scheme.Modules.Hom.app ψ ⊤ m)) =
    q.appTop (Scheme.Modules.Hom.app φ ⊤ m) at hs
  have ht := Scheme.Modules.Hom.app_smul (X := Y) (U := ⊤) t
    (q.appTop (Scheme.Modules.Hom.app ψ ⊤ m)) (1 : Γ(Y, ⊤))
  change (show Γ(Y, ⊤) from Scheme.Modules.Hom.app t ⊤
      (q.appTop (Scheme.Modules.Hom.app ψ ⊤ m) * (1 : Γ(Y, ⊤)) : Γ(Y, ⊤))) =
    q.appTop (Scheme.Modules.Hom.app ψ ⊤ m) *
      (show Γ(Y, ⊤) from Scheme.Modules.Hom.app t ⊤ (1 : Γ(Y, ⊤))) at ht
  rw [mul_one] at ht
  exact (mul_comm _ _).trans (ht.symm.trans hs)

end AlgebraicGeometry.Scheme.Modules.Invertible
