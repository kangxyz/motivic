/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.StalkKernel
public import Motivic.Aglib.AlgebraicGeometry.Intersection.CoefficientStalkTransport
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Support

/-!
# Closed quotient stalks as modules
-/

@[expose] public noncomputable section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.Hom

open _root_.HomologicalComplex.ModuleLengthEuler

/-- The literal closed-immersion ideal quotient retains the original stalk scalar action. -/
def closedStalkQuotientLinearEquiv {E T : Scheme.{u}}
    (j : E ⟶ T) [IsClosedImmersion j] (e : E) :
    ModuleCat.of (T.presheaf.stalk (j e))
        ((T.presheaf.stalk (j e)) ⧸ j.ker.stalk (j e)) ≃ₗ[T.presheaf.stalk (j e)]
      (ModuleCat.restrictScalars (j.stalkMap e).hom).obj
        (ModuleCat.of (E.presheaf.stalk e) (E.presheaf.stalk e)) := by
  let q := (Ideal.quotEquivOfEq (j.ker_stalk e)).trans (stalkQuotientKerEquiv j e)
  refine { q.toAddEquiv with map_smul' := ?_ }
  intro r x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  change q (Ideal.Quotient.mk _ (r * b)) =
    (j.stalkMap e).hom r * q (Ideal.Quotient.mk _ b)
  simp only [q, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    stalkQuotientKerEquiv, RingHom.quotientKerEquivOfSurjective_apply_mk, map_mul]

end AlgebraicGeometry.Scheme.Hom
