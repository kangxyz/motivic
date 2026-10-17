module
public import Motivic.Aglib.RingTheory.PolynomialPresentationWithTailCoordinates

/-! # Actual finite projection of a closed quotient preserving residue minors

The source presentation and every elimination relation are constructed. The final
map has codomain the original affine algebra, with the unchanged closed quotient.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
universe u v w
namespace ParameterizedNoetherNormalization

/-- Construct a finite coordinate map on the entire original closed quotient,
retaining the selected original differential minors at every prescribed residue. -/
theorem exists_finite_quotient_projection_preserving_differential_minors
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (d : ℕ)
    (hd : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type v} [Finite ι] (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (L : (i : ι) → Fin d → R →ₗ[k] K i) (g : Fin d → R)
    (hg : ∀ i, Matrix.det (fun a b => L i a (g b)) ≠ 0) :
    ∃ ψ : MvPolynomial (Fin d) k →ₐ[k] R,
      ((Ideal.Quotient.mkₐ k I).comp ψ).Finite ∧
      ∀ i, Matrix.det (fun a b => L i a (ψ (X b))) ≠ 0 := by
  obtain ⟨e, θ, hθ, htail⟩ := exists_surjective_presentation_with_tail_coordinates k R d g
  let q := (Ideal.Quotient.mkₐ k I).comp θ
  have hq : q.Finite := AlgHom.Finite.of_surjective q
    ((Ideal.Quotient.mkₐ_surjective k I).comp hθ)
  let D (i : ι) (a : Fin d) := (L i a).comp θ.toLinearMap
  have hD : ∀ i, Matrix.det (fun a b => D i a (X (tailCoordinate d e b))) ≠ 0 := by
    intro i
    convert! hg i using 1
    congr 1
    ext a b
    change L i a (θ (X (tailCoordinate d e b))) = L i a (g b)
    rw [htail]
  obtain ⟨φ, hfin, hminor⟩ :=
    exists_iterated_finite_projection_preserving_differential_minors d e q hq hd K D hD
  refine ⟨θ.comp φ, ?_, ?_⟩
  · simpa only [q, AlgHom.comp_assoc] using! hfin
  · simpa only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply] using! hminor

end ParameterizedNoetherNormalization
