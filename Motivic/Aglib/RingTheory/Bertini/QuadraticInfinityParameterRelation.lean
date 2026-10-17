/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityCharts
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveEvaluationDimension

/-! # A genuine nonzero parameter relation for the original quadratic infinity chart -/
@[expose] public noncomputable section
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u}

/-- The full original infinity quotient, not its reduction. -/
abbrev boundaryRing (g : σ → R) (j : Exponent σ) :=
  chart k R g j ⧸ Ideal.span {infinityCoordinate k R g j}

/-- The unchanged monomial ratios on the full infinity boundary. -/
def boundaryCoordinate (g : σ → R) (j e : Exponent σ) : boundaryRing k R g j :=
  Ideal.Quotient.mk _ ⟨ratio k R g j e,
    Algebra.subset_adjoin (Or.inl ⟨e, rfl⟩)⟩

/-- The original normalized homogeneous coordinate is still one on this quotient. -/
theorem boundaryCoordinate_self (g : σ → R) (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) : boundaryCoordinate k R g j j = 1 := by
  have he : (⟨ratio k R g j j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩ :
      chart k R g j) = 1 := Subtype.ext (ratio_self k R g j hj)
  simp only [boundaryCoordinate, he, map_one]

/-- The full chart's actual dimension bound is derived from the original affine domain. -/
theorem trdeg_boundaryRing_le (g : σ → R) (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) {d : ℕ}
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    Algebra.trdeg k (boundaryRing k R g j) ≤ d :=
  trdeg_infinity_quotient_le k R g j hj _
    (Ideal.subset_span (Set.mem_singleton _)) hd

variable [Finite σ]

/-- One nonzero polynomial in the same `(d+1)` quadratic forms vanishes on every
common-zero incidence point of this actual infinity chart. -/
theorem exists_nonzero_infinity_parameter_relation (g : σ → R) (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ f : MvPolynomial (Fin (d + 1) × Exponent σ) k, f ≠ 0 ∧
      ProjectiveEvaluationIncidence.parameterMap (boundaryRing k R g j) k
        (boundaryCoordinate k R g j) (d + 1) f = 0 := by
  apply ProjectiveEvaluationIncidence.exists_nonzero_parameter_relation k
    (boundaryRing k R g j) (boundaryCoordinate k R g j) (d + 1) j
    (boundaryCoordinate_self k R g j hj)
  simpa only [Nat.cast_add, Nat.cast_one] using
    add_le_add (trdeg_boundaryRing_le k R g j hj hd) (le_refl (1 : Cardinal.{u}))

end QuadraticIncidence.InfinityChart
