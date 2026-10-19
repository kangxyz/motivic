/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Transport the unchanged affine whole-fiber smooth open into its actual compactification -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The image of the original affine retained open stays affine and carries
exactly the original relative smooth morphism. -/
theorem affine_smooth_image
    {X N S : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
    (q : N ⟶ S) (f : X ⟶ S) (hi : i ≫ q = f)
    (V : X.Opens) [IsAffine V.toScheme] (n : ℕ)
    [SmoothOfRelativeDimension n (V.ι ≫ f)] :
    IsAffine (i ''ᵁ V).toScheme ∧ SmoothOfRelativeDimension n ((i ''ᵁ V).ι ≫ q) := by
  have ha : IsAffineOpen (i ''ᵁ V) :=
    IsAffineOpen.image_of_isOpenImmersion
      (show IsAffineOpen V from (inferInstance : IsAffine V.toScheme)) i
  refine ⟨ha, ?_⟩
  let e := IsOpenImmersion.isoOfRangeEq (V.ι ≫ i) (i ''ᵁ V).ι
    (by simp [Scheme.Hom.comp_base, Set.range_comp])
  have hs : SmoothOfRelativeDimension n (e.inv ≫ V.ι ≫ f) := by
    simpa only [zero_add] using
      (smoothOfRelativeDimension_comp (n := 0) (m := n) e.inv (V.ι ≫ f))
  have he : e.inv ≫ V.ι ≫ f = (i ''ᵁ V).ι ≫ q := by
    rw [← hi]
    simpa only [Category.assoc] using
      (IsOpenImmersion.isoOfRangeEq_inv_fac_assoc (V.ι ≫ i) (i ''ᵁ V).ι
        (by simp [Scheme.Hom.comp_base, Set.range_comp]) q)
  exact he ▸ hs

/-- Containing the entire original fiber implies containing the entire old-source
fiber in the compactification, not merely the selected point. -/
theorem whole_fiber_image
    {X N S : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
    (q : N ⟶ S) (f : X ⟶ S) (hi : i ≫ q = f)
    (V : X.Opens) (s : S) (hV : ∀ x : X, f x = s → x ∈ V) :
    ∀ x : N, q x = s → x ∈ i.opensRange → x ∈ i ''ᵁ V := by
  intro x hx hxi
  obtain ⟨y, rfl⟩ := hxi
  refine ⟨y, hV y ?_, rfl⟩
  simpa only [← Scheme.Hom.comp_apply, hi] using hx

end AlgebraicGeometry.Scheme.RelativeCurve
