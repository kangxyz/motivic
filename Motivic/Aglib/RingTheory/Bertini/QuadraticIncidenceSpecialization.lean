module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceBaseChange

/-! # Specializing the actual quadratic incidence quotient

A point of the original incidence quotient induces a point after any intermediate
coefficient extension. The construction derives the new equations from the old
quotient, retaining every original parameter coordinate and the original
cotangent module. No field or flatness assumption is needed.
-/
@[expose] public noncomputable section
open MvPolynomial Module TensorProduct KaehlerDifferential
universe u v
namespace QuadraticIncidence

variable (k R A : Type u) [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra R A] {σ : Type v} [Fintype σ]

/-- The images of the original monomial parameter coordinates. -/
def coordinateImages {E : Type u} [CommRing E] [Algebra A E]
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) : Fin d × Exponent σ → E :=
  fun q => h (LinearIncidence.coordinates
    (ProjectiveIncidence.coefficientMatrix (R := A) (coefficientVector k R A g a d w)) q)

/-- The old quotient itself, not an assumed relation, supplies the vanishing vector. -/
theorem coordinateImages_vector_eq_zero [Algebra.Smooth k R]
    {E : Type u} [CommRing E] [Algebra A E]
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) :
    (∑ q, coordinateImages k R A g a d w h q ⊗ₜ[A]
      coefficientVector k R A g a d w q) = 0 := by
  apply (ProjectiveIncidence.equations_iff_vector_eq_zero _ _).mp
  have heval : aeval (coordinateImages k R A g a d w h) =
      h.comp (Ideal.Quotient.mkₐ A (LinearIncidence.ideal
        (ProjectiveIncidence.coefficientMatrix (R := A)
          (coefficientVector k R A g a d w)))) := by
    ext q
    simp [coordinateImages, LinearIncidence.coordinates]
  intro p hp
  rw [RingHom.mem_ker]
  change aeval (coordinateImages k R A g a d w h) p = 0
  rw [heval, AlgHom.comp_apply]
  change h (Ideal.Quotient.mk _ p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

variable (K E : Type u) [CommRing K] [CommRing E]
  [Algebra R K] [Algebra A K] [Algebra R E] [Algebra A E] [Algebra K E]
  [IsScalarTower R A E] [IsScalarTower R K E]
  [IsScalarTower A K E] [Algebra.Smooth k R]

/-- The same coordinate images satisfy the actual intermediate-base incidence
vector equation, with the unchanged original generator and monomial indices. -/
theorem coordinateImages_specialized_vector_eq_zero
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) :
    (∑ q, coordinateImages k R A g a d w h q ⊗ₜ[K]
      coefficientVector k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w) q) = 0 := by
  have hE := (sum_coefficientVector_eq_zero_iff k R A E g a d w
    (coordinateImages k R A g a d w h)).mp
      (coordinateImages_vector_eq_zero k R A g a d w h)
  apply (sum_coefficientVector_eq_zero_iff k R K E g (algebraMap A K ∘ a) d
    (algebraMap A K ∘ w) (coordinateImages k R A g a d w h)).mpr
  have ha : algebraMap K E ∘ (algebraMap A K ∘ a) = algebraMap A E ∘ a := by
    ext i
    exact (IsScalarTower.algebraMap_apply A K E (a i)).symm
  have hw : algebraMap K E ∘ (algebraMap A K ∘ w) = algebraMap A E ∘ w := by
    ext i
    exact (IsScalarTower.algebraMap_apply A K E (w i)).symm
  simpa only [ha, hw] using hE

/-- Every defining equation of the intermediate-base quotient lies in the kernel
of evaluation at the original coordinate images. -/
theorem specialized_ideal_le_ker
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) :
    LinearIncidence.ideal (ProjectiveIncidence.coefficientMatrix (R := K)
      (coefficientVector k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w))) ≤
        RingHom.ker (aeval (coordinateImages k R A g a d w h)).toRingHom :=
  (ProjectiveIncidence.equations_iff_vector_eq_zero _ _).mpr
    (coordinateImages_specialized_vector_eq_zero k R A K E g a d w h)

/-- The actual intermediate-base specialization homomorphism of incidence quotients. -/
def specialize
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) :
    CoordinateRing k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w) →ₐ[K] E :=
  Ideal.Quotient.liftₐ _ (aeval (coordinateImages k R A g a d w h))
    (fun _ hp => RingHom.mem_ker.mp (specialized_ideal_le_ker k R A K E g a d w h hp))

/-- Specialization preserves the literal image of every original parameter variable. -/
@[simp]
theorem specialize_coordinates
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) (q : Fin d × Exponent σ) :
    specialize k R A K E g a d w h
      (LinearIncidence.coordinates (ProjectiveIncidence.coefficientMatrix (R := K)
        (coefficientVector k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w))) q) =
      h (LinearIncidence.coordinates (ProjectiveIncidence.coefficientMatrix (R := A)
        (coefficientVector k R A g a d w)) q) := by
  change aeval (coordinateImages k R A g a d w h) (X q) = _
  rw [aeval_X]
  rfl

end QuadraticIncidence
