/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.AlgebraicSimplexPolynomial
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # Units on every algebraic simplex over a reduced ring -/

@[expose] public noncomputable section

universe u

namespace Motivic.AlgebraicSimplex

variable (R : Type u) [CommRing R] [IsReduced R]

/-- Every unit of every actual simplex coordinate ring is a constant unit.
Reduced rings need not be fields, domains, connected, or nonzero. -/
theorem constant_units_bijective (n : ℕ) :
    Function.Bijective (Units.map (constant R n).toMonoidHom) := by
  constructor
  · intro x y h
    apply Units.ext
    have he := congrArg (fun z : (CoordinateRing R n)ˣ =>
      polynomialEquiv R n (z : CoordinateRing R n)) h
    change polynomialProjection R n (constant R n (x : R)) =
      polynomialProjection R n (constant R n (y : R)) at he
    rw [polynomialProjection_constant, polynomialProjection_constant] at he
    exact MvPolynomial.C_injective (Fin n) R he
  · intro x
    have h := x.isUnit.map (polynomialEquiv R n).toRingHom
    obtain ⟨r, ⟨v, hv⟩, hr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
    refine ⟨v, Units.ext ?_⟩
    apply (polynomialEquiv R n).injective
    change polynomialProjection R n (constant R n (v : R)) = _
    rw [polynomialProjection_constant, hv]
    exact hr.symm

/-- The canonical constant-units isomorphism in every simplex degree. -/
def constantUnitsEquiv (n : ℕ) : Rˣ ≃* (CoordinateRing R n)ˣ :=
  MulEquiv.ofBijective (Units.map (constant R n).toMonoidHom) (constant_units_bijective R n)

@[simp] theorem constantUnitsEquiv_apply (n : ℕ) (x : Rˣ) :
    constantUnitsEquiv R n x = Units.map (constant R n).toMonoidHom x := rfl

/-- Every simplex operator becomes the identity under constant-unit identification. -/
theorem constantUnitsEquiv_pullback {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (x : Rˣ) :
    Units.map (pullback R f).toMonoidHom (constantUnitsEquiv R n x) =
      constantUnitsEquiv R m x := by
  apply Units.ext
  exact pullback_constant R f x

end Motivic.AlgebraicSimplex
