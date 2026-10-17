/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.AdaptedPolynomialChart
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual affine Cartier-divisor chart squares

The mapped ideal is used literally, so the Cartesian closed subscheme retains
its original scheme structure and not only its underlying support.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The quotient by the literal extended ideal is the actual schematic pullback. -/
theorem isPullback_Spec_quotient_map
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map (algebraMap A B))
        (algebraMap A B) (Ideal.le_comap_map))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  apply isPullback_SpecMap_of_isPushout
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm
  apply (CommRingCat.isPushout_tensorProduct A B (A ⧸ I)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
  · simp
  · simp
  · ext b
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm
      (b ⊗ₜ[A] (1 : A ⧸ I)) = _
    simpa using Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul B I b 1
  · ext a
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm
      (1 ⊗ₜ[A] (Ideal.Quotient.mk I a)) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    simp [Algebra.smul_def]

/-- Equality with the extended ideal identifies the original quotient as the
Cartesian closed subscheme, rather than merely identifying its support. -/
theorem exists_isPullback_Spec_quotient_of_map_eq
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map f = J) :
    ∃ z : Spec (.of (B ⧸ J)) ⟶ Spec (.of (A ⧸ I)),
      IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) z
        (Spec.map (CommRingCat.ofHom f))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  subst J
  let : Algebra A B := f.toAlgebra
  exact ⟨_, isPullback_Spec_quotient_map A B I⟩

/-- The actual étale adapted chart, its entire original closed divisor, and
its unchanged principal-open complement are obtained together. -/
theorem exists_affine_etale_chart_preserving_principal_divisor
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (t : R) (ht : IsRegular t) [Algebra.FormallySmooth k (R ⧸ Ideal.span {t})]
    (p : Ideal R) [p.IsPrime] (htp : t ∈ p) :
    ∃ (s : Set R) (hts : t ∈ s), s.Finite ∧ ∃ r ∉ p,
      let B := Localization.Away r
      let P := MvPolynomial s k
      let φ : P →+* B := (algebraMap R B).comp
        (MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R))).toRingHom
      let T : P := .X ⟨t, hts⟩
      let tB : B := algebraMap R B t
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ z : Spec (.of (B ⧸ Ideal.span {tB})) ⟶ Spec (.of (P ⧸ Ideal.span {T})),
        IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {tB})))) z
          (Spec.map (CommRingCat.ofHom φ))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {T})))) ∧
        Etale z ∧
        Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen T =
          PrimeSpectrum.basicOpen tB := by
  obtain ⟨s, hts, hs, r, hr, hφ⟩ :=
    Algebra.exists_etale_polynomial_chart_preserving_regular_generator k R t ht p htp
  refine ⟨s, hts, hs, r, hr, ?_⟩
  dsimp only
  let φ := (algebraMap R (Localization.Away r)).comp
    (MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R))).toRingHom
  have hT : φ (.X ⟨t, hts⟩) = algebraMap R (Localization.Away r) t := by
    simp only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X]
  have hmap : (Ideal.span {MvPolynomial.X (R := k) (⟨t, hts⟩ : s)}).map φ =
      Ideal.span {algebraMap R (Localization.Away r) t} := by
    rw [Ideal.map_span, Set.image_singleton, hT]
  have he : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
  obtain ⟨z, hz⟩ := exists_isPullback_Spec_quotient_of_map_eq φ _ _ hmap
  refine ⟨he, z, hz, MorphismProperty.of_isPullback hz he, ?_⟩
  rw [SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen hT

end AlgebraicGeometry.Scheme
