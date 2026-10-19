/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.ZeroRow
/-! # Literal quotient compatibility for the unchanged quadratic functions -/
@[expose] public noncomputable section
open AlgebraicGeometry _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

omit [Fintype σ] in
/-- Original affine generators still generate the literal quotient, with all nilpotents. -/
theorem quadraticGenerators_quotient (I : Ideal R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Algebra.adjoin k (Set.range (Ideal.Quotient.mk I ∘ g)) = ⊤ := by
  change Algebra.adjoin k (Set.range ((Ideal.Quotient.mkₐ k I) ∘ g)) = ⊤
  rw [Set.range_comp, Algebra.adjoin_image, hg, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective k I)

/-- The coordinate map commutes literally with the original quotient map. -/
theorem quadraticCoordinateHom_quotient (I : Ideal R) (c : Fin d × Exponent σ → k) :
    quadraticCoordinateHom k (R ⧸ I) (Ideal.Quotient.mk I ∘ g) d c =
      (Ideal.Quotient.mk I).comp (quadraticCoordinateHom k R g d c) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [quadraticCoordinateHom]
  · intro i
    simpa [quadraticCoordinateHom, Function.comp_def] using
      (MvPolynomial.comp_aeval_apply g (Ideal.Quotient.mkₐ k I)
        (parameterTuple k σ d c i).val).symm

end QuadraticIncidence.InfinityChart
