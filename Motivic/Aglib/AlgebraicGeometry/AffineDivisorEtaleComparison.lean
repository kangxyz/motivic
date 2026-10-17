/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PolynomialZeroFiberSquare
public import Motivic.Aglib.AlgebraicGeometry.EtaleDiagonalNeighborhood
public import Motivic.Aglib.RingTheory.Etale.AdaptedPolynomialCylinder
public import Aglib.Algebra.Polynomial.Laurent.BaseChange

/-! # Actual common étale neighborhoods of an affine divisor and its zero section -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Remove the off-diagonal from the actual product of a polynomial chart and
the cylinder on its entire zero fiber. Both closed fibers remain the original
scheme `Spec D`, with identity vertical maps. -/
theorem exists_common_etale_neighborhood_of_polynomial_chart
    {H B D : Type u} [CommRing H] [CommRing B] [CommRing D]
    (ψ : Polynomial H →+* B) (hψ : ψ.Etale)
    (q : B →+* D) (σ : H →+* D)
    (hq : Function.Surjective q) (hk : RingHom.ker q = Ideal.span {ψ Polynomial.X})
    (hσ : (q.comp ψ).comp Polynomial.C = σ) :
    ∃ (V : Scheme.{u}) (a : V ⟶ Spec (.of B)) (b : V ⟶ Spec (.of (Polynomial D)))
      (j : Spec (.of D) ⟶ V), Etale a ∧ Etale b ∧
      IsPullback j (𝟙 _) a (Spec.map (CommRingCat.ofHom q)) ∧
      IsPullback j (𝟙 _) b (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))) ∧
      IsIso (pullback.snd a (Spec.map (CommRingCat.ofHom q))) ∧
      IsIso (pullback.snd b (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)))) := by
  let f := Spec.map (CommRingCat.ofHom ψ)
  let g := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ))
  let r := Spec.map (CommRingCat.ofHom σ)
  have hf : Etale f := HasRingHomProperty.Spec_iff.mpr hψ
  have hX := isPullback_polynomial_zero_of_surjective ψ q σ hq hk hσ
  have hr : Etale r := MorphismProperty.of_isPullback hX hf
  have hg : Etale g := MorphismProperty.of_isPullback
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.PolynomialLaurent.polynomial_isPushout (CommRingCat.ofHom σ))) hr
  have hY := isPullback_polynomial_zero_of_surjective (Polynomial.mapRingHom σ)
    (Polynomial.evalRingHom (0 : D)) σ
    (fun d ↦ ⟨Polynomial.C d, by simp⟩)
    (by simp [Polynomial.ker_evalRingHom]) (by ext d; simp)
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective _ hq
  obtain ⟨U, j, ha, hb, h₁, h₂, hi₁, hi₂⟩ :=
    exists_common_etale_neighborhood_of_cartesian_charts r f g
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : D))))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : H)))) hX hY
  exact ⟨U.toScheme, U.ι ≫ pullback.fst f g, U.ι ≫ pullback.snd f g,
    j, ha, hb, h₁, h₂, hi₁, hi₂⟩

/-- Near every prime of a smooth regular principal divisor, the actual pair
has a common étale neighborhood with the zero section of its own affine-line
cylinder. The whole original localized quotient is retained on both sides.
No chosen coordinate chart, retraction, or residue-field condition is assumed. -/
theorem exists_etale_comparison_with_divisor_cylinder
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (t : R) (ht : IsRegular t) [Algebra.FormallySmooth k (R ⧸ Ideal.span {t})]
    (p : Ideal R) [p.IsPrime] (htp : t ∈ p) :
    ∃ r ∉ p,
      let B := Localization.Away r
      let D := B ⧸ Ideal.span {algebraMap R B t}
      ∃ (V : Scheme.{u}) (a : V ⟶ Spec (.of B)) (b : V ⟶ Spec (.of (Polynomial D)))
        (j : Spec (.of D) ⟶ V), Etale a ∧ Etale b ∧
        IsPullback j (𝟙 _) a
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap R B t})))) ∧
        IsPullback j (𝟙 _) b (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))) ∧
        IsIso (pullback.snd a
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap R B t}))))) ∧
        IsIso (pullback.snd b (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)))) := by
  obtain ⟨ι, _, r, hr, ψ, hψ, hψX⟩ :=
    Algebra.exists_etale_polynomial_cylinder_preserving_regular_generator k R t ht p htp
  refine ⟨r, hr, ?_⟩
  let q := Ideal.Quotient.mk (Ideal.span {algebraMap R (Localization.Away r) t})
  exact exists_common_etale_neighborhood_of_polynomial_chart ψ hψ q
    ((q.comp ψ).comp Polynomial.C) Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker, hψX]) rfl

end AlgebraicGeometry.Scheme
