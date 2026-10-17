/-
Copyright (c) 2026 Motivic Cohomology Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.AlgebraicSimplex
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial coordinates on the algebraic simplex

Eliminating the final barycentric coordinate gives an explicit algebra
isomorphism between the `n`-simplex coordinate ring and `R[t₀, …, tₙ₋₁]`.
The other coordinates are retained in their original order. In particular the
construction is a polynomial algebra in every degree, including degree zero.
The formulas also supply an integral-domain instance over an integral base.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

namespace Motivic.AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The chosen scalar map is the canonical quotient-algebra map. -/
theorem constant_eq_algebraMap (n : ℕ) :
    constant R n = algebraMap R (CoordinateRing R n) := rfl

/-- The final coordinate is determined by the other coordinates. -/
theorem coordinate_last (n : ℕ) :
    coordinate R n (Fin.last n) = 1 - ∑ i : Fin n, coordinate R n i.castSucc := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [Fin.sum_univ_castSucc, add_comm] using sum_coordinate R n

/-- Eliminate the final coordinate to obtain ordinary polynomial coordinates. -/
def polynomialProjection (n : ℕ) : CoordinateRing R n →+* MvPolynomial (Fin n) R :=
  lift MvPolynomial.C
    (Fin.lastCases (1 - ∑ i, MvPolynomial.X i) MvPolynomial.X) (by
      simp [Fin.sum_univ_castSucc])

/-- Insert the first `n` barycentric coordinates into the simplex ring. -/
def polynomialInclusion (n : ℕ) : MvPolynomial (Fin n) R →+* CoordinateRing R n :=
  MvPolynomial.eval₂Hom (constant R n) (fun i ↦ coordinate R n i.castSucc)

@[simp]
theorem polynomialProjection_constant (n : ℕ) (r : R) :
    polynomialProjection R n (constant R n r) = MvPolynomial.C r :=
  lift_constant _ _ _ _

@[simp]
theorem polynomialProjection_coordinate_castSucc (n : ℕ) (i : Fin n) :
    polynomialProjection R n (coordinate R n i.castSucc) = MvPolynomial.X i := by
  simp [polynomialProjection]

@[simp]
theorem polynomialProjection_coordinate_last (n : ℕ) :
    polynomialProjection R n (coordinate R n (Fin.last n)) =
      1 - ∑ i, MvPolynomial.X i := by
  simp [polynomialProjection]

@[simp]
theorem polynomialInclusion_C (n : ℕ) (r : R) :
    polynomialInclusion R n (MvPolynomial.C r) = constant R n r := by
  simp [polynomialInclusion]

@[simp]
theorem polynomialInclusion_X (n : ℕ) (i : Fin n) :
    polynomialInclusion R n (MvPolynomial.X i) = coordinate R n i.castSucc := by
  simp [polynomialInclusion]

@[simp]
theorem polynomialProjection_comp_inclusion (n : ℕ) :
    (polynomialProjection R n).comp (polynomialInclusion R n) =
      RingHom.id (MvPolynomial (Fin n) R) := by
  apply MvPolynomial.ringHom_ext <;> intro i <;> simp

@[simp]
theorem polynomialInclusion_comp_projection (n : ℕ) :
    (polynomialInclusion R n).comp (polynomialProjection R n) =
      RingHom.id (CoordinateRing R n) := by
  apply ringHom_ext
  · intro r
    simp
  · intro i
    cases i using Fin.lastCases with
    | last => simp [coordinate_last]
    | cast i => simp

/-- The canonical quotient is a polynomial algebra in `n` independent coordinates. -/
def polynomialEquiv (n : ℕ) : CoordinateRing R n ≃ₐ[R] MvPolynomial (Fin n) R :=
  { RingEquiv.ofRingHom (polynomialProjection R n) (polynomialInclusion R n)
      (polynomialProjection_comp_inclusion R n) (polynomialInclusion_comp_projection R n) with
    commutes' r := polynomialProjection_constant R n r }

@[simp]
theorem polynomialEquiv_coordinate_castSucc (n : ℕ) (i : Fin n) :
    polynomialEquiv R n (coordinate R n i.castSucc) = MvPolynomial.X i :=
  polynomialProjection_coordinate_castSucc R n i

@[simp]
theorem polynomialEquiv_coordinate_last (n : ℕ) :
    polynomialEquiv R n (coordinate R n (Fin.last n)) =
      1 - ∑ i, MvPolynomial.X i :=
  polynomialProjection_coordinate_last R n

/-- The simplex over an integral domain has an integral coordinate ring. -/
instance [IsDomain R] (n : ℕ) : IsDomain (CoordinateRing R n) :=
  (polynomialEquiv R n).toMulEquiv.isDomain (MvPolynomial (Fin n) R)

end Motivic.AlgebraicSimplex
