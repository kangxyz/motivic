/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineBoundaryRefinement
public import Mathlib.AlgebraicGeometry.Noetherian

/-! The genuine affine refinement in its canonical Spec presentation. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
/-- The original étale leg has an actual affine-Spec refinement retaining the entire boundary.
Neither the base nor its chosen open is changed. -/
theorem exists_spec_etale_boundary_refinement {k : Type u} [Field k]
    {Z Y X : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : IsPullback s (𝟙 Z) p z)
    (q : Z ⟶ Spec (.of k)) [IsFinite q] :
    ∃ (R : CommRingCat.{u}) (r : Spec R ⟶ Y) (t : Z ⟶ Spec R),
      IsOpenImmersion r ∧ t ≫ r = s ∧
        IsPullback t (𝟙 Z) (r ≫ p) z ∧ Etale (r ≫ p) := by
  obtain ⟨U, hU, t, ht, _, _⟩ := exists_affine_etale_boundary_refinement p z s hs q
  let : IsAffine U.toScheme := hU
  let r := U.toScheme.isoSpec.inv ≫ U.ι
  let t' := t ≫ U.toScheme.isoSpec.hom
  have ht' : t' ≫ r = s := by simp [t', r, ht]
  exact ⟨Γ(U.toScheme, ⊤), r, t', inferInstance, ht',
    isPullback_boundary_refinement p z s hs r t' ht', inferInstance⟩

/-- Over the original locally Noetherian base, the actual source ring satisfies Serre's
Noetherian hypothesis rather than requiring it as new input. -/
theorem exists_noetherian_spec_etale_boundary_refinement {k : Type u} [Field k]
    {Z Y X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X]
    (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : IsPullback s (𝟙 Z) p z)
    (q : Z ⟶ Spec (.of k)) [IsFinite q] :
    ∃ (R : CommRingCat.{u}) (r : Spec R ⟶ Y) (t : Z ⟶ Spec R),
      IsNoetherianRing R ∧ IsOpenImmersion r ∧ t ≫ r = s ∧
        IsPullback t (𝟙 Z) (r ≫ p) z ∧ Etale (r ≫ p) := by
  obtain ⟨R, r, t, hr, ht, H, he⟩ := exists_spec_etale_boundary_refinement p z s hs q
  let : Etale (r ≫ p) := he
  have : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian (r ≫ p)
  exact ⟨R, r, t, isLocallyNoetherian_Spec.mp this, hr, ht, H, he⟩
end AlgebraicGeometry.Scheme
