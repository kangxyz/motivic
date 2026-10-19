module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineBoundaryRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine neighborhoods retaining a full section after one base shrink

The base is shrunk by a single principal open.  The complete scheme-theoretic
section is retained, without a finiteness or reducedness assumption on it.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- An affine refinement near a section point retains the full section over a
principal neighborhood of that point of the original base. -/
theorem exists_affine_section_principal_refinement
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of R)) (z : Spec (.of R) ⟶ Y)
    (hz : z ≫ q = 𝟙 _) (s : Spec (.of R)) :
    ∃ (r : R) (V : Y.Opens), s ∈ PrimeSpectrum.basicOpen r ∧
      IsAffineOpen V ∧ V ≤ q ⁻¹ᵁ PrimeSpectrum.basicOpen r ∧
      ∃ t : Scheme.Opens.toScheme (X := Spec (.of R))
          (PrimeSpectrum.basicOpen r) ⟶ V.toScheme,
        IsPullback t (Scheme.Opens.ι (X := Spec (.of R))
          (PrimeSpectrum.basicOpen r)) V.ι z := by
  obtain ⟨U, hU, hsU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show z s ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hsr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show s ∈ z ⁻¹ᵁ U from hsU) (z ⁻¹ᵁ U).isOpen
  let V : Y.Opens := U ⊓ q ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have hV : IsAffineOpen V := by
    let : IsAffine U.toScheme := hU
    have h := (IsAffineOpen.Spec_basicOpen r).preimage (U.ι ≫ q)
    have hh := h.image_of_isOpenImmersion U.ι
    have heq : U.ι ''ᵁ ((U.ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r) = V := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι]
    exact heq ▸ hh
  have he : z ⁻¹ᵁ V = PrimeSpectrum.basicOpen r := by
    ext x
    change (z x ∈ U ∧ q (z x) ∈ PrimeSpectrum.basicOpen r) ↔ _
    have hx : q (z x) = x := congrArg (fun f : Spec (.of R) ⟶ Spec (.of R) => f x) hz
    rw [hx]
    exact ⟨fun h => h.2, fun h => ⟨hrU h, h⟩⟩
  let e := (Spec (.of R)).isoOfEq he.symm
  refine ⟨r, V, hsr, hV, inf_le_right, e.hom ≫ (z ∣_ V), ?_⟩
  apply (isPullback_morphismRestrict z V).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using (Spec (.of R)).isoOfEq_hom_ι he.symm
  · simp
  · simp

/-- An actual étale neighborhood of a section has an affine refinement retaining
its entire closed fiber over one principal shrink of the original base. -/
theorem exists_affine_etale_section_principal_refinement
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (i : Spec (.of R) ⟶ X)
    (hi : i ≫ π = 𝟙 _) (p : Y ⟶ X) [Etale p]
    (z : Spec (.of R) ⟶ Y) (hp : IsPullback z (𝟙 _) p i)
    (s : Spec (.of R)) :
    ∃ (r : R) (V : Y.Opens), s ∈ PrimeSpectrum.basicOpen r ∧
      IsAffineOpen V ∧ V ≤ (p ≫ π) ⁻¹ᵁ PrimeSpectrum.basicOpen r ∧
      Etale (V.ι ≫ p) ∧
      ∃ t : Scheme.Opens.toScheme (X := Spec (.of R))
          (PrimeSpectrum.basicOpen r) ⟶ V.toScheme,
        IsPullback t (Scheme.Opens.ι (X := Spec (.of R))
          (PrimeSpectrum.basicOpen r)) (V.ι ≫ p) i := by
  have hz : z ≫ (p ≫ π) = 𝟙 _ := by
    rw [← Category.assoc, hp.w, Category.id_comp, hi]
  obtain ⟨r, V, hr, hV, hVr, t, ht⟩ :=
    exists_affine_section_principal_refinement (p ≫ π) z hz s
  refine ⟨r, V, hr, hV, hVr, inferInstance, t, ?_⟩
  simpa only [Category.comp_id] using ht.paste_vert hp

end AlgebraicGeometry.Scheme
