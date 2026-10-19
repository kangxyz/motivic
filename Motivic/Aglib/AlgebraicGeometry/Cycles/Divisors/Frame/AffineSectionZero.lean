/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.AffineRegularPrincipalScalar
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts

/-!
# The original section zero scheme in an affine line-bundle frame

One actual frame gives the original scalar, its regularity for a monic section
map, and an isomorphism from its original whole zero scheme to the literal
principal quotient. Applying these constructions to two maps with the same
frame preserves their common scalar coordinates. No source integrality enters.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineSectionZero`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineGenericRatio`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.AffineNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (B : CommRingCat.{u}) (L : LineBundle (Spec B))
  (φ : (show (Spec B).Modules from L.val) ⟶
    (show (Spec B).Modules from SheafOfModules.unit (Spec B).ringCatSheaf))
  (e : L.val.over ⊤ ≅ SheafOfModules.unit ((Spec B).ringCatSheaf.over ⊤))

/-- The specified section map's scalar in the specified actual affine frame. -/
def affineFrameScalar : B :=
  (ΓSpecIso B).hom (Scheme.Modules.Hom.app φ ⊤ (chartGenerator (Spec B) L.val ⊤ e))

/-- A monic section map has a regular scalar in this same frame. -/
theorem affineFrameScalar_mem_nonZeroDivisors [Mono φ] :
    affineFrameScalar B L φ e ∈ nonZeroDivisors B := by
  have hr := (app_injective_iff_chart_regular L φ ⊤ e ⊤ le_rfl).mp
    (moduleHom_app_injective φ ⊤)
  simp only [homOfLE_refl, op_id] at hr
  rw [mem_nonZeroDivisors_iff_left]
  intro b hb
  apply (ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
  apply hr
  change _ * (ΓSpecIso B).inv b = _ * (ΓSpecIso B).inv 0
  have h := congrArg (fun x : B => (ΓSpecIso B).inv x) hb
  simpa [affineFrameScalar, map_mul] using h

/-- Equality of the actual ideal sheaves of the original zero scheme and the
literal quotient by its same-frame scalar, retaining nilpotents. -/
theorem zeroInclusion_ker_eq_affineFrameQuotient :
    (Hom.zeroInclusion φ).ker =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {affineFrameScalar B L φ e})))).ker := by
  apply IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.principalQuotient_kernel_top]
  have h := zeroInclusion_kernel_eq_span_chart L φ ⊤ e
    ⟨⊤, isAffineOpen_top (Spec B)⟩ le_rfl
  simpa [affineFrameScalar] using h

/-- The original whole section zero scheme is the original scalar's principal
quotient, by the native closed-immersion lift from the proved ideal equality. -/
def affineFrameZeroSchemeIso :
    Hom.zeroScheme φ ≅ Spec (.of (B ⧸ Ideal.span {affineFrameScalar B L φ e})) := by
  let i := Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {affineFrameScalar B L φ e})))
  have h : i.ker = (Hom.zeroInclusion φ).ker :=
    (zeroInclusion_ker_eq_affineFrameQuotient B L φ e).symm
  let : IsIso (IsClosedImmersion.lift i (Hom.zeroInclusion φ) h.le) :=
    IsClosedImmersion.isIso_lift i (Hom.zeroInclusion φ) h
  exact asIso (IsClosedImmersion.lift i (Hom.zeroInclusion φ) h.le)

/-- The quotient comparison commutes with the literal original zero inclusion. -/
@[reassoc]
theorem affineFrameZeroSchemeIso_hom_inclusion :
    (affineFrameZeroSchemeIso B L φ e).hom ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {affineFrameScalar B L φ e}))) =
      Hom.zeroInclusion φ := by
  exact IsClosedImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme.Modules.Invertible
