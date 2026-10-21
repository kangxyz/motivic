/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# Original whole section zero cycles under scheme isomorphisms

The comparison is the actual zero-scheme base-change isomorphism followed by
the original pullback projection. In particular this applies to the canonical
affine global-section spectrum isomorphism, without replacing a zero cycle.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Fundamental.SectionZeroCycleIso`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineSchemeSectionNormCycle`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.SectionZeroCycleOpenBaseChange`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme

/-- The Noetherian instance used in this module. -/
local instance sectionZeroCycleIsoNoetherian {X : Scheme.{u}} [IsNoetherian X]
    {M : X.Modules} (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    IsNoetherian (Scheme.Modules.Hom.zeroScheme φ) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion φ)

/-- The original whole zero cycle is transported by the actual scheme
isomorphism and its canonical pulled section map. -/
theorem residuePushforward_zeroScheme_iso
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (e : X ≅ Y) {M : Y.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward e.hom
        (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit φ e.hom))
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle
            (Scheme.Modules.Hom.zeroScheme (Scheme.Modules.Hom.pullbackToUnit φ e.hom)))) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (Scheme.Modules.Hom.zeroInclusion φ)
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme φ)) :=
            by
  let E := Scheme.Modules.Hom.zeroSchemePullbackIso φ e.hom ≪≫
    asIso (pullback.snd e.hom (Scheme.Modules.Hom.zeroInclusion φ))
  have hE : E.hom ≫ Scheme.Modules.Hom.zeroInclusion φ =
      Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit φ e.hom) ≫
        e.hom := by
    dsimp only [E, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, ← pullback.condition,
      Scheme.Modules.Hom.zeroSchemePullbackIso_hom_fst_assoc]
  rw [← AddMonoidHom.comp_apply, ←
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp, ← hE,
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
        AddMonoidHom.comp_apply,
    _root_.AlgebraicGeometry.Scheme.residuePushforward_fundamentalPointCycle]

end AlgebraicGeometry.Scheme
