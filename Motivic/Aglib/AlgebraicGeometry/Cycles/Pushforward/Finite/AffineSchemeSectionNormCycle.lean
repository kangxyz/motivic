/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.SectionZeroCycleIso
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineNormCycle
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General

/-!
# Norm cycles on the original finite affine scheme

The canonical global-section spectrum comparison transports both original zero
schemes. No replacement-cycle equality is supplied. The one specified frame is
on the canonical pullback of the original line bundle.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineSchemeSectionNormCycle`.
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

local instance {X : Scheme.{u}} [IsNoetherian X]
    {M : X.Modules} (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    IsNoetherian (Scheme.Modules.Hom.zeroScheme φ) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion φ)

/-- Original finite-affine section zero cycles have the determinant norm ratio
computed in one frame on their canonical global-section spectrum. -/
theorem residuePushforward_affineScheme_section_norm_ratio
    (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {C : Scheme.{u}} [IsAffine C] (p : C ⟶ Spec A) [IsFinite p]
    (L : LineBundle C)
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
    (e : (pullbackLineBundle C.isoSpec.inv L).val.over ⊤ ≅
      SheafOfModules.unit ((Spec Γ(C, ⊤)).ringCatSheaf.over ⊤)) :
    letI : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType p
    let : Algebra A Γ(C, ⊤) := (FiniteSchemeNormBaseChange.scalarMap p).toAlgebra
    ∀ [Module.Free A Γ(C, ⊤)],
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward p
          (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
              (Scheme.Modules.Hom.zeroInclusion φ)
              (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
                  φ)) -
            _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
                (Scheme.Modules.Hom.zeroInclusion ψ)
              (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
                  ψ))) =
        _root_.PrimeSpectrum.FiniteFiber.affinePrincipalOrderCycle A
          (Algebra.norm A (affineFrameScalar Γ(C, ⊤) (pullbackLineBundle C.isoSpec.inv L)
            (pullbackUnitMap C.isoSpec.inv φ) e))
          (Algebra.norm A (affineFrameScalar Γ(C, ⊤) (pullbackLineBundle C.isoSpec.inv L)
            (pullbackUnitMap C.isoSpec.inv ψ) e)) := by
  let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType p
  let : Algebra A Γ(C, ⊤) := (FiniteSchemeNormBaseChange.scalarMap p).toAlgebra
  let : Module.Finite A Γ(C, ⊤) := FiniteSchemeNormBaseChange.sections_finite p
  let : IsNoetherianRing Γ(C, ⊤) := IsNoetherianRing.of_finite A Γ(C, ⊤)
  dsimp only
  intro hfree
  let : Module.Free A Γ(C, ⊤) := hfree
  let : L.val.IsLocallyFree := lineBundle_isLocallyFree C L
  let : L.val.IsQuasicoherent := inferInstance
  let L' := pullbackLineBundle C.isoSpec.inv L
  let φ' := pullbackUnitMap C.isoSpec.inv φ
  let ψ' := pullbackUnitMap C.isoSpec.inv ψ
  let : Mono φ' := by dsimp [φ', pullbackUnitMap]; infer_instance
  let : Mono ψ' := by dsimp [ψ', pullbackUnitMap]; infer_instance
  have hp : Spec.map (CommRingCat.ofHom (algebraMap A Γ(C, ⊤)) : A ⟶ Γ(C, ⊤)) =
      C.isoSpec.inv ≫ p := by
    change Spec.map ((Scheme.ΓSpecIso A).inv ≫ p.appTop) = _
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
    exact Scheme.isoSpec_inv_naturality p
  have h := _root_.AlgebraicGeometry.Scheme.residuePushforward_affineFrame_section_norm_ratio A Γ(C,
      ⊤) L' φ' ψ' e
  rw [hp, _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
      AddMonoidHom.comp_apply,
    map_sub] at h
  erw [_root_.AlgebraicGeometry.Scheme.residuePushforward_zeroScheme_iso C.isoSpec.symm φ,
    _root_.AlgebraicGeometry.Scheme.residuePushforward_zeroScheme_iso C.isoSpec.symm ψ] at h
  exact h

end AlgebraicGeometry.Scheme
