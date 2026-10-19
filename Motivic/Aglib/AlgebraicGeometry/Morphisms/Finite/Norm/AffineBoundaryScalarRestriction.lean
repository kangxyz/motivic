/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
/-! # Scalar restriction on the whole affine-chart boundary

The actual pullback over an affine chart detects equality on the whole inverse
image open. No reducedness or residue-field detection is involved.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.AffineBoundaryScalarRestriction`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.NormalizedUnit`, `Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- Equality on a boundary fiber pulls back through a commuting ambient square.
The whole ambient square need not be Cartesian. -/
theorem pullback_scalar_eq_one_of_comm
    {R : Type u} [CommRing R] {E D T P : Scheme.{u}}
    (e : E ⟶ T) (r : E ⟶ D) (d : D ⟶ P) (t : T ⟶ P)
    (he : e ≫ t = r ≫ d) (w : Spec (.of R) ⟶ T) (μ : R)
    (h : scalarMap (pullback.snd d (w ≫ t)) μ = 1) :
    scalarMap (pullback.snd e w) μ = 1 := by
  let l : pullback e w ⟶ pullback d (w ≫ t) :=
    pullback.lift (pullback.fst e w ≫ r) (pullback.snd e w) (by
      rw [Category.assoc, ← he, ← Category.assoc, pullback.condition,
        Category.assoc])
  have hh := congrArg (fun x => l.appTop x) h
  change l.appTop ((pullback.snd d (w ≫ t)).appTop
    ((Scheme.ΓSpecIso (.of R)).inv μ)) = l.appTop 1 at hh
  rw [map_one, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop] at hh
  dsimp only [l] at hh
  rw [pullback.lift_snd] at hh
  exact hh

/-- Equality to one after the canonical affine-chart pullback is equality on
all of the original inverse-image open, including its nilpotent structure. -/
theorem app_eq_one_of_affine_pullback_scalar_eq_one
    {D T : Scheme.{u}} (d : D ⟶ T) (U : T.Opens) (hU : IsAffineOpen U)
    (μ : Γ(T, U))
    (h : scalarMap (pullback.snd d hU.fromSpec) μ = 1) :
    d.app U μ = 1 := by
  let l : (d ⁻¹ᵁ U).toScheme ⟶ pullback d hU.fromSpec :=
    pullback.lift (d ⁻¹ᵁ U).ι ((d ∣_ U) ≫ hU.isoSpec.hom) (by
      simp only [IsAffineOpen.fromSpec, Category.assoc, Iso.hom_inv_id_assoc,
        morphismRestrict_ι])
  have hs : (d ∣_ U).appTop (U.topIso.inv μ) = 1 := by
    have hh := congrArg (fun x => l.appTop x) h
    change l.appTop ((pullback.snd d hU.fromSpec).appTop
      ((Scheme.ΓSpecIso Γ(T, U)).inv μ)) = l.appTop 1 at hh
    rw [map_one, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop] at hh
    dsimp only [l] at hh
    rw [pullback.lift_snd, Scheme.Hom.comp_appTop, hU.isoSpec_hom_appTop] at hh
    simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] using hh
  have he : U.topIso.hom ≫ d.app U =
      (d ∣_ U).appTop ≫ (d ⁻¹ᵁ U).topIso.hom := by
    have hh := (arrowResLEAppIso d U (d ⁻¹ᵁ U) le_rfl).hom.w
    change U.topIso.hom ≫ d.appLE U (d ⁻¹ᵁ U) le_rfl =
      (d.resLE U (d ⁻¹ᵁ U) le_rfl).appTop ≫ (d ⁻¹ᵁ U).topIso.hom at hh
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.appLE_eq_app] using hh
  have hv := congrArg (fun k : Γ(U.toScheme, ⊤) ⟶ Γ(D, d ⁻¹ᵁ U) =>
    k (U.topIso.inv μ)) he
  simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, hs, map_one] using hv

/-- A scalar equality on the original boundary chart gives equality on the
actual Cartesian product boundary, before any coproduct gluing. -/
theorem app_eq_one_of_isPullback_affine_scalar_eq_one
    {E D T P : Scheme.{u}} (e : E ⟶ T) (r : E ⟶ D)
    (d : D ⟶ P) (t : T ⟶ P) (H : IsPullback r e d t)
    (U : T.Opens) (hU : IsAffineOpen U) (μ : Γ(T, U))
    (h : scalarMap (pullback.snd d (hU.fromSpec ≫ t)) μ = 1) :
    e.app U μ = 1 :=
  app_eq_one_of_affine_pullback_scalar_eq_one e U hU μ
    (pullback_scalar_eq_one_of_comm e r d t H.w.symm hU.fromSpec μ h)

end AlgebraicGeometry.FiniteSchemeNormBaseChange
