/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IntersectionAmbientIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Canonical affine quotient charts of actual closed intersections

The actual section map of a closed immersion identifies its affine inverse
image with the quotient by its literal ideal-sheaf component. For a Cartesian
intersection this kernel is the sum of the two original closed ideals. The
coordinate equivalence retains the original section map, rather than choosing
an unrelated quotient chart. This is a ring-chart construction, not a Tor sheaf.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Intersection

variable {P T : Scheme.{u}} (i : T ⟶ P) [IsClosedImmersion i]

/-- The literal affine section quotient of a closed immersion. -/
def closedAffineQuotientEquiv (U : P.affineOpens) :
    Γ(P, U) ⧸ i.ker.ideal U ≃+* Γ(T, i ⁻¹ᵁ U) :=
  (Ideal.quotEquivOfEq (i.ker_apply U)).trans
    ((i.app U).hom.quotientKerEquivOfSurjective (i.app_surjective U U.2))

/-- The constructed quotient chart retains the original ambient section map. -/
@[simp] theorem closedAffineQuotientEquiv_mk (U : P.affineOpens) (r : Γ(P, U)) :
    closedAffineQuotientEquiv i U (Ideal.Quotient.mk (i.ker.ideal U) r) = i.app U r := by
  simp only [closedAffineQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The quotient identification is compatible with the actual scalar ring map. -/
theorem closedAffineQuotientEquiv_comp_mk (U : P.affineOpens) :
    (closedAffineQuotientEquiv i U).toRingHom.comp (Ideal.Quotient.mk (i.ker.ideal U)) =
      (i.app U).hom := by
  ext r
  exact closedAffineQuotientEquiv_mk i U r

omit [IsClosedImmersion i] in
/-- Affine restriction carries the actual closed ideal to the actual smaller ideal. -/
theorem closedAffineIdeal_map {U V : P.affineOpens} (h : U ≤ V) :
    (i.ker.ideal V).map (P.presheaf.map (homOfLE h).op).hom = i.ker.ideal U :=
  i.ker.map_ideal h

/-- The literal quotient ring map induced by an affine refinement. -/
def closedAffineQuotientRestriction {U V : P.affineOpens} (h : U ≤ V) :
    Γ(P, V) ⧸ i.ker.ideal V →+* Γ(P, U) ⧸ i.ker.ideal U :=
  Ideal.quotientMap (i.ker.ideal U) (P.presheaf.map (homOfLE h).op).hom
    (i.ker.ideal_le_comap_ideal h)

omit [IsClosedImmersion i] in
/-- The quotient refinement sends each actual section class to its restriction. -/
@[simp] theorem closedAffineQuotientRestriction_mk {U V : P.affineOpens}
    (h : U ≤ V) (r : Γ(P, V)) :
    closedAffineQuotientRestriction i h (Ideal.Quotient.mk (i.ker.ideal V) r) =
      Ideal.Quotient.mk (i.ker.ideal U) (P.presheaf.map (homOfLE h).op r) := rfl

/-- The canonical quotient-chart isomorphisms respect the actual source restrictions. -/
theorem closedAffineQuotientEquiv_naturality {U V : P.affineOpens}
    (h : U ≤ V) (x : Γ(P, V) ⧸ i.ker.ideal V) :
    closedAffineQuotientEquiv i U (closedAffineQuotientRestriction i h x) =
      T.presheaf.map (homOfLE (i.preimage_mono h)).op (closedAffineQuotientEquiv i V x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [closedAffineQuotientRestriction_mk, closedAffineQuotientEquiv_mk]
  exact ConcreteCategory.congr_hom (i.naturality (homOfLE h).op) r

omit [IsClosedImmersion i] in
/-- Identity refinements give the identity quotient ring map. -/
@[simp] theorem closedAffineQuotientRestriction_refl (U : P.affineOpens) :
    closedAffineQuotientRestriction i (show U ≤ U from le_rfl) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  change Ideal.Quotient.mk _ ((P.presheaf.map (𝟙 (Opposite.op U.1))).hom r) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

omit [IsClosedImmersion i] in
/-- Successive affine refinements have the exact quotient-ring composition law. -/
theorem closedAffineQuotientRestriction_comp {U V W : P.affineOpens}
    (h : U ≤ V) (k : V ≤ W) :
    (closedAffineQuotientRestriction i h).comp (closedAffineQuotientRestriction i k) =
      closedAffineQuotientRestriction i (h.trans k) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, closedAffineQuotientRestriction_mk]
  congr 1
  exact (ConcreteCategory.congr_hom (P.presheaf.map_comp (homOfLE (show V.1 ≤ W.1 from k)).op
    (homOfLE (show U.1 ≤ V.1 from h)).op) r).symm

variable {W D : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T) (j : D ⟶ P)
  [IsClosedImmersion j] (sq : IsPullback a b j i)

include sq

/-- The actual intersection section kernel is the sum of both original ideals. -/
theorem closedIntersectionAffineKernel (U : P.affineOpens) :
    RingHom.ker ((a ≫ j).app U).hom = j.ker.ideal U ⊔ i.ker.ideal U := by
  have : IsClosedImmersion a := by
    rw [← sq.isoPullback_hom_fst]
    infer_instance
  rw [← Scheme.Hom.ker_apply]
  exact congrArg (fun I : P.IdealSheafData => I.ideal U)
    (Motivic.ker_comp_eq_sup_of_isPullback a b j i sq)

/-- The whole affine intersection inverse image has its literal sum-ideal quotient. -/
def closedIntersectionAffineQuotientEquiv (U : P.affineOpens) :
    Γ(P, U) ⧸ (j.ker.ideal U ⊔ i.ker.ideal U) ≃+* Γ(W, (a ≫ j) ⁻¹ᵁ U) := by
  have : IsClosedImmersion a := by
    rw [← sq.isoPullback_hom_fst]
    infer_instance
  exact (Ideal.quotEquivOfEq (closedIntersectionAffineKernel i a b j sq U).symm).trans
    (((a ≫ j).app U).hom.quotientKerEquivOfSurjective
      ((a ≫ j).app_surjective U U.2))

/-- The canonical intersection quotient square preserves actual section scalars. -/
theorem closedIntersectionAffineQuotientEquiv_mk (U : P.affineOpens)
    (r : Γ(P, U)) :
    closedIntersectionAffineQuotientEquiv i a b j sq U
      (Ideal.Quotient.mk (j.ker.ideal U ⊔ i.ker.ideal U) r) = (a ≫ j).app U r := by
  simp only [closedIntersectionAffineQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end Motivic.Intersection
