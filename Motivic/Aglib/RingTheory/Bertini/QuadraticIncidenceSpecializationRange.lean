module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceSpecialization

/-! # The original incidence image is contained in its actual specialization

The original coefficient algebra already maps through the intermediate field.
Together with preservation of the literal parameter coordinates, this implies
that every original incidence element lies in the specialized image.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial Module TensorProduct KaehlerDifferential
universe u v
namespace QuadraticIncidence
variable (k R A K E : Type u) [CommRing k] [CommRing R] [CommRing A]
  [CommRing K] [CommRing E] [Algebra k R] [Algebra R A]
  [Algebra R K] [Algebra A K] [Algebra R E] [Algebra A E] [Algebra K E]
  [IsScalarTower R A E] [IsScalarTower R K E]
  [IsScalarTower A K E] [Algebra.Smooth k R]
  {σ : Type v} [Fintype σ]

/-- No field-generation assumption is needed: the original quotient is generated
by its actual coefficient algebra and the unchanged monomial parameters. -/
theorem image_mem_specialize_range
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E)
    (c : CoordinateRing k R A g a d w) :
    h c ∈ (specialize k R A K E g a d w h).range := by
  let f := specialize k R A K E g a d w h
  have ht : (⊤ : Subalgebra A (CoordinateRing k R A g a d w)) ≤
      (f.range.restrictScalars A).comap h := by
    rw [← LinearIncidence.adjoin_coordinates_eq_top
      (ProjectiveIncidence.coefficientMatrix (R := A) (coefficientVector k R A g a d w))]
    apply Algebra.adjoin_le
    rintro _ ⟨q, rfl⟩
    exact ⟨_, specialize_coordinates k R A K E g a d w h q⟩
  exact ht (show c ∈ (⊤ : Subalgebra A (CoordinateRing k R A g a d w)) from trivial)

end QuadraticIncidence
