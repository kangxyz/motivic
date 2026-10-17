module
import Motivic.Aglib.AlgebraicGeometry.ClosedBoundaryFiniteCoordinates
/-! # Direct finite projection on the full original closed quotient -/
open CategoryTheory AlgebraicGeometry

example (k R : Type) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] R),
      Function.Injective ((Ideal.Quotient.mkₐ k I).comp f) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom)) :=
  Scheme.exists_closedBoundary_finite_projection k R I hI
