/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.AlgebraicIndependent.LinearRelationsTrdeg
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual polynomial quotient imposing incidence equations

The equations are literal linear polynomials in the parameter coefficients.
Their quotient supplies the relations used by the transcendence-degree bound;
no relation or dimension assumption is supplied for that quotient.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u v w
namespace LinearIncidence
variable {R : Type u} [CommRing R] {N : Type v} [Fintype N] {Q : Type w}

/-- One actual linear equation in the universal parameter coordinates. -/
def equation (A : Matrix Q N R) (q : Q) : MvPolynomial N R :=
  ∑ i, C (A q i) * X i

/-- The ideal of the full linear incidence equations. -/
def ideal (A : Matrix Q N R) : Ideal (MvPolynomial N R) :=
  Ideal.span (Set.range (equation A))

/-- The literal universal incidence algebra, with its original parameters. -/
abbrev CoordinateRing (A : Matrix Q N R) := MvPolynomial N R ⧸ ideal A

/-- The universal parameter coefficients in the incidence quotient. -/
def coordinates (A : Matrix Q N R) (i : N) : CoordinateRing A :=
  Ideal.Quotient.mk (ideal A) (X i)

/-- Every original row equation holds in the full quotient, including its nilpotents. -/
theorem equations_hold (A : Matrix Q N R) :
    (A.map (algebraMap R (CoordinateRing A))).mulVec (coordinates A) = 0 := by
  ext q
  have h : Ideal.Quotient.mk (ideal A) (equation A q) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨q, rfl⟩)
  simpa [equation, coordinates, Matrix.mulVec, dotProduct] using! h

/-- The unchanged parameter coordinates generate the actual incidence quotient. -/
theorem adjoin_coordinates_eq_top (A : Matrix Q N R) :
    Algebra.adjoin R (Set.range (coordinates A)) = ⊤ := by
  rw [← MvPolynomial.aeval_range]
  apply (AlgHom.range_eq_top _).mpr
  have hmap : aeval (coordinates A) = Ideal.Quotient.mkₐ R (ideal A) := by
    ext i
    simp [coordinates]
  rw [hmap]
  exact Ideal.Quotient.mk_surjective

end LinearIncidence
