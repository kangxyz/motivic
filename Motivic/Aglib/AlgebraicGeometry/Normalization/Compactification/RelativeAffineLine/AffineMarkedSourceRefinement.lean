/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.QuasiAffine.FiniteSupportBaseNeighborhood

/-! # An affine original étale source retaining the whole marked fiber

The auxiliary affine-target normalization proves quasi-affinity only. No
identification with the later compactification of the refined cover is made.


Intended upstream module:
Module prefix: `Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.`
Module suffix: `AffineMarkedSourceRefinement`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.Diagrams.AffineRefinement`,
`Motivic.Transfers.Presheaf.Sheafification.Representatives.Restriction`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Refine the original source before choosing compactifications or sections.
The full nonreduced marked scheme is restricted only along the coefficient base,
and its actual Cartesian square is preserved. -/
theorem exists_affine_marked_source_refinement
    (R : Type u) [CommRing R] [IsDomain R]
    {X Y Z : Scheme.{u}} [IsAffine X]
    (q : X ⟶ Spec (.of R)) (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
    (z : Z ⟶ X) [IsFinite (z ≫ q)] (s : Z ⟶ Y) (hs : s ≫ p = z)
    (H : IsPullback s (𝟙 Z) p z) :
    ∃ (r : R), r ≠ 0 ∧ ∃ (W : Y.Opens) (_hW : IsAffineOpen W)
      (hW : W ≤ p ⁻¹ᵁ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r)),
      ∃ t : ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ⟶ W.toScheme,
        t ≫ W.ι = ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫ s ∧
        IsPullback t (𝟙 _)
          (p.resLE (q ⁻¹ᵁ PrimeSpectrum.basicOpen r) W hW)
          (z ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r)) := by
  have : Y.IsQuasiAffine := isQuasiAffine_of_etale_affine_target p
  have : IsFinite (s ≫ (p ≫ q)) := by rw [← Category.assoc, hs]; infer_instance
  obtain ⟨r, hr, W, hWa, hW, t, ht⟩ :=
    exists_affine_finite_support_base_neighborhood (p ≫ q) s
  have he : s ≫ (p ≫ q) = z ≫ q := by rw [← Category.assoc, hs]
  let e := Z.isoOfEq (congrArg (fun f => f ⁻¹ᵁ PrimeSpectrum.basicOpen r) he.symm)
  let t' := e.hom ≫ t
  have htι : t' ≫ W.ι = ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫ s := by
    dsimp only [t']
    rw [Category.assoc, ht.w, ← Category.assoc]
    rw [Scheme.isoOfEq_hom_ι]
  have ht' : IsPullback t' ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι W.ι s := by
    exact ht.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [t', Iso.refl_hom, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.comp_id]; exact Scheme.isoOfEq_hom_ι _ _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  have hW' : W ≤ p ⁻¹ᵁ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r) := hW
  let p' := p.resLE (q ⁻¹ᵁ PrimeSpectrum.basicOpen r) W hW'
  have hc : t' ≫ p' = (𝟙 _) ≫ (z ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r)) := by
    apply (cancel_mono (q ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).mp
    simp only [Category.assoc, p', Scheme.Hom.resLE_comp_ι,
      Category.id_comp, morphismRestrict_ι]
    rw [← Category.assoc, htι, Category.assoc, hs]
    rfl
  have ho : IsPullback t' ((𝟙 _) ≫ ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι)
      (p' ≫ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι) z := by
    simpa only [Category.id_comp, p', Scheme.Hom.resLE_comp_ι, Category.comp_id] using
      ht'.paste_vert H
  exact ⟨r, hr, W, hWa, hW', t', htι,
    ho.of_bot hc (isPullback_morphismRestrict z (q ⁻¹ᵁ PrimeSpectrum.basicOpen r))⟩

end AlgebraicGeometry.Scheme
