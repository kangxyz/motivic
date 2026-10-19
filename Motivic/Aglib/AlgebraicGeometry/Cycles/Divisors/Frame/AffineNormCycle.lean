/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineSectionZero
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCycle
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance

/-!
# Norm cycles of two original section maps in one affine frame

The source cycles are the fundamental cycles of the original whole zero schemes.
Their exact inclusion isomorphisms identify them with scalar quotients in the same
specified frame. Monicity supplies scalar regularity; source integrality and
reducedness are not assumed. The frame is produced locally on the whole finite
preimage by `exists_principal_frame_of_finite_free`.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineNormCycle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineSchemeSectionNormCycle`.
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

/-- Transport of the original whole zero cycle through the exact same-frame
quotient isomorphism, with the literal original zero inclusion retained. -/
theorem residuePushforward_affineFrame_zeroScheme
    (B : CommRingCat.{u}) [IsNoetherianRing B] (L : LineBundle (Spec B))
    (φ : (show (Spec B).Modules from L.val) ⟶
      (show (Spec B).Modules from SheafOfModules.unit (Spec B).ringCatSheaf))
    (e : L.val.over ⊤ ≅ SheafOfModules.unit ((Spec B).ringCatSheaf.over ⊤)) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (Scheme.Modules.Hom.zeroInclusion φ)
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme φ)) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {affineFrameScalar B L φ e}))))
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle
          (Spec (.of (B ⧸ Ideal.span {affineFrameScalar B L φ e})))) := by
  rw [← affineFrameZeroSchemeIso_hom_inclusion B L φ e,
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
        AddMonoidHom.comp_apply,
    _root_.AlgebraicGeometry.Scheme.residuePushforward_fundamentalPointCycle]
  rfl

/-- Finite pushforward of the two original zero cycles is the existing principal
cycle of their actual determinant norm ratio in one and the same affine frame. -/
theorem residuePushforward_affineFrame_section_norm_ratio
    (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : LineBundle (Spec B))
    (φ ψ : (show (Spec B).Modules from L.val) ⟶
      (show (Spec B).Modules from SheafOfModules.unit (Spec B).ringCatSheaf))
    [Mono φ] [Mono ψ]
    (e : L.val.over ⊤ ≅ SheafOfModules.unit ((Spec B).ringCatSheaf.over ⊤)) :
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B))
        (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion φ)
            (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
                φ)) -
          _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
              (Scheme.Modules.Hom.zeroInclusion ψ)
            (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme
                ψ))) =
      _root_.PrimeSpectrum.FiniteFiber.affinePrincipalOrderCycle A
        (Algebra.norm A (affineFrameScalar B L φ e))
        (Algebra.norm A (affineFrameScalar B L ψ e)) := by
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  rw [residuePushforward_affineFrame_zeroScheme B L φ e,
    residuePushforward_affineFrame_zeroScheme B L ψ e]
  exact _root_.PrimeSpectrum.FiniteFiber.residuePushforward_regular_cartier_norm_ratio A B _ _
    (affineFrameScalar_mem_nonZeroDivisors B L φ e)
    (affineFrameScalar_mem_nonZeroDivisors B L ψ e)

end AlgebraicGeometry.Scheme
