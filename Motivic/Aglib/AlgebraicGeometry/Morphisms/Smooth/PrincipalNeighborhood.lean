/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.SourceLocal.PrincipalNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth principal neighborhoods
-/

@[expose] public noncomputable section

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry

/-- Smoothness of relative dimension on localized affine neighborhoods glues to
one principal open containing the whole closed subscheme. -/
theorem exists_principal_smooth_neighborhood
    (A R : Type u) [CommRing A] [CommRing R] (φ : A →+* R) (J : Ideal R) (n : ℕ)
    (h : ∀ x : PrimeSpectrum R, J ≤ x.asIdeal →
      ∃ a ∉ x.asIdeal, SmoothOfRelativeDimension n
        (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away a)).comp φ)))) :
    ∃ r : R, r - 1 ∈ J ∧ SmoothOfRelativeDimension n
      ((Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ≫
        Spec.map (CommRingCat.ofHom φ)) := by
  apply exists_principal_neighborhood_of_local_property R
    (Spec.map (CommRingCat.ofHom φ)) (@SmoothOfRelativeDimension n) J
  intro x hx
  obtain ⟨a, ha, hPa⟩ := h x hx
  refine ⟨a, ha, ?_⟩
  have H := IsZariskiLocalAtSource.comp hPa (basicOpenIsoSpecAway (R := .of R) a).hom
  rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap (R := .of R)] at H
  exact H

end AlgebraicGeometry
