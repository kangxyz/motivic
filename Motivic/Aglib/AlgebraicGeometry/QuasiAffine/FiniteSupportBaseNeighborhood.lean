/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.QuasiAffine.FiniteNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Original affine neighborhoods retaining a full finite support

A finite fiber of a proper support is a finite subset of the original scheme.
An affine neighborhood of its image therefore exists in the original quasi-affine
ambient scheme. Removing the closed image of the missed support and shrinking
the base to a principal neighborhood retains the entire support scheme, including
nilpotents. No generic-fiber model or reduced support is substituted.


Intended upstream module: `Aglib.AlgebraicGeometry.QuasiAffine.FiniteSupportBaseNeighborhood`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.AffineMarkedSourceRefinement`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme

/-- An original affine ambient open retains the whole proper support after a
principal base restriction near any point with finite support fiber. -/
theorem exists_affine_support_principal_neighborhood
    {R : Type u} [CommRing R] {X Z : Scheme.{u}} [X.IsQuasiAffine]
    (q : X ⟶ Spec (.of R)) (z : Z ⟶ X) [IsProper (z ≫ q)]
    (x : Spec (.of R)) (hx : ((z ≫ q) ⁻¹' {x}).Finite) :
    ∃ r : R, x ∈ PrimeSpectrum.basicOpen r ∧
      ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ q ⁻¹ᵁ PrimeSpectrum.basicOpen r ∧
        ∃ t : ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ⟶ W.toScheme,
          IsPullback t ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι W.ι z := by
  let f := z ≫ q
  obtain ⟨A, hA, hAf⟩ := exists_isAffineOpen_of_finite
    (z '' (f ⁻¹' {x})) (hx.image z)
  let bad : Set (Spec (.of R)) := f '' (z ⁻¹' (A : Set X))ᶜ
  have hbad : IsClosed bad :=
    f.isClosedMap _ (z.continuous.isOpen_preimage _ A.isOpen).isClosed_compl
  let O : (Spec (.of R)).Opens := ⟨badᶜ, hbad.isOpen_compl⟩
  have hxO : x ∈ O := by
    rintro ⟨a, ha, hax⟩
    exact ha (hAf ⟨a, hax, rfl⟩)
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hxr, hrO⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxO O.isOpen
  let W : X.Opens := A ⊓ q ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have hW : IsAffineOpen W := by
    let : IsAffine A.toScheme := hA
    have h := (IsAffineOpen.Spec_basicOpen r).preimage (A.ι ≫ q)
    have hh := h.image_of_isOpenImmersion A.ι
    have heq : A.ι ''ᵁ ((A.ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r) = W := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι]
    exact heq ▸ hh
  have he : z ⁻¹ᵁ W = f ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
    ext a
    change (z a ∈ A ∧ q (z a) ∈ PrimeSpectrum.basicOpen r) ↔
      f a ∈ PrimeSpectrum.basicOpen r
    constructor
    · exact fun h => h.2
    · intro ha
      refine ⟨?_, ha⟩
      by_contra hn
      exact hrO ha ⟨a, hn, rfl⟩
  let e := Z.isoOfEq he.symm
  refine ⟨r, hxr, W, hW, inf_le_right, e.hom ≫ (z ∣_ W), ?_⟩
  apply (isPullback_morphismRestrict z W).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using Z.isoOfEq_hom_ι he.symm
  · simp
  · simp

/-- A finite-over-base support is retained in an original affine open after one
nonzero principal restriction of an integral affine base. The full support is
base changed, not replaced by its reduced generic fiber. -/
theorem exists_affine_finite_support_base_neighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    {X Z : Scheme.{u}} [X.IsQuasiAffine]
    (q : X ⟶ Spec (.of R)) (z : Z ⟶ X) [IsFinite (z ≫ q)] :
    ∃ r : R, r ≠ 0 ∧
      ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ q ⁻¹ᵁ PrimeSpectrum.basicOpen r ∧
        ∃ t : ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ⟶ W.toScheme,
          IsPullback t ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι W.ι z := by
  obtain ⟨r, hr, W, hW, hWr, t, ht⟩ :=
    exists_affine_support_principal_neighborhood q z (genericPoint (Spec (.of R)))
      ((z ≫ q).finite_preimage (Set.finite_singleton _))
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    simp at hr
  exact ⟨r, hr0, W, hW, hWr, t, ht⟩

end AlgebraicGeometry.Scheme
