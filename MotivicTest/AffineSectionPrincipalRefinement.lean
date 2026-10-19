module
import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineSectionPrincipalRefinement
import Mathlib.Algebra.Polynomial.Eval.Defs
/-! # The actual zero-section étale-neighborhood consumer -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

example (R : Type) [CommRing R] {Y : Scheme}
    (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p]
    (z : Spec (.of R) ⟶ Y)
    (hp : IsPullback z (𝟙 _) p
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))))
    (s : Spec (.of R)) :
    ∃ (r : R) (V : Y.Opens), s ∈ PrimeSpectrum.basicOpen r ∧
      IsAffineOpen V ∧
      V ≤ (p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen r ∧ Etale (V.ι ≫ p) ∧
      ∃ t : Scheme.Opens.toScheme (X := Spec (.of R))
          (PrimeSpectrum.basicOpen r) ⟶ V.toScheme,
        IsPullback t (Scheme.Opens.ι (X := Spec (.of R))
          (PrimeSpectrum.basicOpen r)) (V.ι ≫ p)
          (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) := by
  apply Scheme.exists_affine_etale_section_principal_refinement
    (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) _ p z hp s
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by
    ext x
    simp
  rw [h, Spec.map_id]
