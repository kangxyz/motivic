/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Stalk

/-!
# Order cancellation for the original ideal in its specified frame

The scalar is extracted from the original ideal inclusion and the specified
frame, not chosen as an unrelated local equation. Its principal ideal is the
actual closed-subscheme kernel; its stalk quotient length therefore keeps the
original multiplicity. A unit numerator cancels this length even when the
canonical ideal section vanishes on the boundary. The affine frame neighborhood
is explicit and no parameter base is changed. Integral-component assumptions
are explicit; disconnected assembly and global moving remain separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite Order
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {C D : Scheme.{u}} (i : D ⟶ C)

/-- The original ideal inclusion evaluated on the generator of the specified frame. -/
def idealFrameScalar (W : C.Opens)
    (e : (idealModule i).over W ≅ SheafOfModules.unit (C.ringCatSheaf.over W)) : Γ(C, W) :=
  (idealInclusion i).app W (chartGenerator C (idealModule i) W e)

/-- The actual section-image ideal of the inclusion is its original ring kernel. -/
theorem sectionImageIdeal_idealInclusion (W : C.Opens) :
    Modules.Hom.sectionImageIdeal (idealInclusion i) W = RingHom.ker (i.app W).hom := by
  ext r
  constructor
  · rintro ⟨m, rfl⟩
    exact congrArg (fun v => v.val.app (op W) m) (idealInclusion_structureMap i)
  · intro hr
    refine ⟨(idealSectionsEquiv i W).symm ⟨r, hr⟩, ?_⟩
    exact (idealSectionsEquiv_val i W _).symm.trans
      (congrArg Subtype.val ((idealSectionsEquiv i W).apply_symm_apply ⟨r, hr⟩))

/-- The specified frame gives the principal equation of the original kernel. -/
theorem ker_app_eq_span_idealFrameScalar
    (hI : IsLocallyRankOne C (idealModule i)) (W : C.Opens)
    (e : (idealModule i).over W ≅ SheafOfModules.unit (C.ringCatSheaf.over W)) :
    RingHom.ker (i.app W).hom = Ideal.span {idealFrameScalar i W e} := by
  rw [← sectionImageIdeal_idealInclusion]
  simpa only [idealFrameScalar, homOfLE_refl, CategoryTheory.op_id, C.presheaf.map_id,
    CommRingCat.id_apply] using
      sectionImageIdeal_eq_span_chart (⟨idealModule i, hI⟩ : LineBundle C)
        (idealInclusion i) W e W le_rfl

/-- The canonical equation is nonzero on a nonempty frame chart. -/
theorem idealFrameScalar_ne_zero (W : C.Opens) [Nonempty W]
    (e : (idealModule i).over W ≅ SheafOfModules.unit (C.ringCatSheaf.over W)) :
    idealFrameScalar i W e ≠ 0 := by
  have hinj := moduleHom_app_injective (idealInclusion i) W
  intro hr
  have hg : chartGenerator C (idealModule i) W e = 0 :=
    hinj (hr.trans (by simp))
  have hc := congrArg (chartSectionEquiv C (idealModule i) W e W le_rfl) hg
  exact one_ne_zero (by
    simpa only [chartGenerator, LinearEquiv.apply_symm_apply, map_zero] using hc)

/-- The original ideal-sheaf stalk is the principal ideal of this exact equation. -/
theorem ker_stalk_eq_span_idealFrameScalar [IsClosedImmersion i]
    (hI : IsLocallyRankOne C (idealModule i)) (W : C.affineOpens)
    (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
    {x : C} (hx : x ∈ W.val) :
    i.ker.stalk x = Ideal.span {C.presheaf.germ W.val x hx (idealFrameScalar i W.val e)} := by
  rw [i.ker.stalk_eq_map W hx, i.ker_apply,
    ker_app_eq_span_idealFrameScalar i hI W.val e, Ideal.map_span, Set.image_singleton]

/-- The original closed-subscheme quotient length is canceled by the rational
frame ratio in the same function field. No unit property of that ratio is used. -/
theorem ideal_quotient_length_add_ord_unit_ratio_eq_zero
    [IsIntegral C] [IsLocallyNoetherian C] [IsClosedImmersion i]
    (hI : IsLocallyRankOne C (idealModule i)) (W : C.affineOpens) [Nonempty W.val]
    (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
    (b : Γ(C, W.val)) (hb : IsUnit b) {x : C} (hxW : x ∈ W.val)
    (hx : coheight x = 1) :
    ((Module.length (C.presheaf.stalk x)
        ((C.presheaf.stalk x) ⧸ i.ker.stalk x)).toNat : ℤ) +
      C.ord (C.germToFunctionField W.val b /
        C.germToFunctionField W.val (idealFrameScalar i W.val e)) x = 0 := by
  rw [ker_stalk_eq_span_idealFrameScalar i hI W e hxW]
  exact C.quotient_length_add_ord_unit_ratio_eq_zero W.val _ b
    (idealFrameScalar_ne_zero i W.val e) hb hxW hx

end AlgebraicGeometry.Scheme.Hom
