/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteTor
public import Motivic.RingTheory.MvPolynomial.Diagonal

/-!
# Genuine finite Koszul resolutions of polynomial diagonals

For every dimension and every commutative coefficient ring, the proved finite
coordinate-difference regular sequence gives an actual projective resolution
of the polynomial diagonal quotient. Genuine Tor against this quotient is
computed by the finite Koszul complex on any coefficient module.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Motivic.PolynomialDiagonal

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The finite ordered list of all coordinate differences. -/
def differences : List (Ambient R (Fin n)) := (List.finRange n).map (difference R (Fin n))

@[simp]
theorem differences_length : (differences R n).length = n := by
  simp [differences]

/-- The finite list generates exactly the actual diagonal ideal. -/
theorem ofList_differences : Ideal.ofList (differences R n) = ideal R (Fin n) := by
  unfold Ideal.ofList ideal
  congr 1
  ext p
  simp [differences]

/-- The full finite diagonal-difference list is weakly regular over any commutative base. -/
theorem differences_isWeaklyRegular :
    RingTheory.Sequence.IsWeaklyRegular (Ambient R (Fin n)) (differences R n) :=
  isWeaklyRegular_differences R (Fin n) (List.finRange n) (List.nodup_finRange n)

/-- The genuine finite Koszul projective resolution of the dimension-n polynomial diagonal. -/
def finiteDiagonalProjectiveResolution :
    ProjectiveResolution (ModuleCat.of (Ambient R (Fin n))
      (Ambient R (Fin n) ⧸ ideal R (Fin n))) := by
  rw [← ofList_differences]
  exact Koszul.finiteProjectiveResolution (differences R n) (differences_isWeaklyRegular R n)

/-- Actual Tor against a polynomial diagonal is finite Koszul homology
with arbitrary coefficients. -/
def finiteDiagonalTorIsoHomology (M : ModuleCat (Ambient R (Fin n))) (i : ℕ) :
    ((Tor (ModuleCat (Ambient R (Fin n))) i).obj M).obj
      (ModuleCat.of _ (Ambient R (Fin n) ⧸ ideal R (Fin n))) ≅
        (Koszul.coefficientComplex M (differences R n)).homology i := by
  rw [← ofList_differences]
  exact Koszul.finiteTorIsoHomology M (differences R n) (differences_isWeaklyRegular R n) i

/-- The diagonal Tor groups vanish above the polynomial dimension. -/
theorem isZero_finiteDiagonalTor_above (M : ModuleCat (Ambient R (Fin n)))
    (i : ℕ) (hi : n < i) :
    IsZero (((Tor (ModuleCat (Ambient R (Fin n))) i).obj M).obj
      (ModuleCat.of _ (Ambient R (Fin n) ⧸ ideal R (Fin n)))) := by
  rw [← ofList_differences]
  exact Koszul.isZero_finiteTor_above_length M (differences R n)
    (differences_isWeaklyRegular R n) i (by simpa only [differences_length] using hi)

end Motivic.PolynomialDiagonal
