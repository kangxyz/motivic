/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.AffineRetainedImage
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PrincipalRetainedBoundary

/-! # Retaining the original affine smooth fiber and prescribed scheme in one compact curve -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- A genuine compactification and an unchanged whole-fiber affine open give one
principal base neighborhood controlling the complete new boundary and prescribed scheme. -/
theorem exists_compact_retained_principal_neighborhood
    (R : Type u) [CommRing R] {X N D Z : Scheme.{u}}
    (i : X ⟶ N) [IsOpenImmersion i] (q : N ⟶ Spec (.of R)) [IsProper q]
    (f : X ⟶ Spec (.of R)) (hi : i ≫ q = f)
    (b : D ⟶ N) [IsFinite (b ≫ q)] (hb : Set.range b = (Set.range i)ᶜ)
    (V : X.Opens) [IsAffine V.toScheme] [SmoothOfRelativeDimension 1 (V.ι ≫ f)]
    (s : Spec (.of R)) (hV : ∀ x : X, f x = s → x ∈ V)
    (z : Z ⟶ X) [IsFinite (z ≫ f)] :
    ∃ t : R, s ∈ PrimeSpectrum.basicOpen t ∧
      IsAffine (i ''ᵁ V).toScheme ∧
      SmoothOfRelativeDimension 1 ((i ''ᵁ V).ι ≫ q) ∧
      IsFinite ((retainedBoundaryInclusion (i ''ᵁ V) ≫ q) ∣_ PrimeSpectrum.basicOpen t) ∧
      IsAffine ((((i ''ᵁ V).ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen t).toScheme) ∧
      ∀ x : Z, (z ≫ f) x ∈ PrimeSpectrum.basicOpen t → (z ≫ i) x ∈ i ''ᵁ V := by
  obtain ⟨ha, hs⟩ := affine_smooth_image i q f hi V 1
  have : IsAffine (i ''ᵁ V).toScheme := ha
  have hz : IsFinite ((z ≫ i) ≫ q) := by
    simpa only [Category.assoc, hi] using (inferInstance : IsFinite (z ≫ f))
  obtain ⟨t, ht, hb', ha', hz'⟩ :=
    exists_principal_finite_retainedBoundary_preserving_scheme R q b
      i.opensRange (i ''ᵁ V) (by simpa only [Scheme.Hom.coe_opensRange] using hb.ge) s
      (whole_fiber_image i q f hi V s hV) (z ≫ i)
      (by rintro _ ⟨x, rfl⟩; exact ⟨z x, rfl⟩)
  refine ⟨t, ht, ha, hs, hb', ha', ?_⟩
  intro x hx
  apply hz' x
  simpa only [Category.assoc, hi] using hx

end AlgebraicGeometry.Scheme.RelativeCurve
