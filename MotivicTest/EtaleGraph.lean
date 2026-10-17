/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.AffineEtale
public import Mathlib.Data.ZMod.Basic

/-!
# Actual graph consumers with arbitrary, nonreduced, and disconnected sources

These consumers instantiate polynomial target charts for arbitrary graph maps,
including graphs whose source coefficient ring has nilpotents or is a product.
The scalar-action test uses the original diagonal list on the graph coefficient
ring, not merely a separately chosen regular presentation of its kernel.
-/

@[expose] public noncomputable section

open RingTheory.Sequence AlgebraicGeometry
open Motivic.PolynomialTensorGraph

namespace Motivic.MotivicTest.EtaleGraph

/-- An arbitrary polynomial map has the claimed actual local graph kernel. -/
theorem polynomial_localGraph (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (g : MvPolynomial (Fin n) R →ₐ[R] A) (p : Ideal A) [p.IsPrime] :
    letI := g.toAlgebra
    let f := Algebra.ofId (MvPolynomial (Fin n) R) A
    IsRegular (Localization.AtPrime (graphPrime R (Fin n) A (MvPolynomial (Fin n) R) f p))
      ((List.finRange n).map (localDifference R (Fin n) A (MvPolynomial (Fin n) R) f p)) ∧
    RingHom.ker (localEvaluation R (Fin n) A (MvPolynomial (Fin n) R) f p) =
      Ideal.ofList
        ((List.finRange n).map (localDifference R (Fin n) A (MvPolynomial (Fin n) R) f p)) := by
  let := g.toAlgebra
  exact etale_localGraphPresentation R (Fin n) A (MvPolynomial (Fin n) R)
    (Algebra.ofId (MvPolynomial (Fin n) R) A) p (List.finRange n)
      (List.nodup_finRange n) List.mem_finRange

/-- A nonreduced source is retained in the genuine local graph construction. -/
theorem nonreduced_localGraph (n : ℕ) (g : MvPolynomial (Fin n) ℤ →ₐ[ℤ] ZMod 4)
    (p : Ideal (ZMod 4)) [p.IsPrime] :
    letI := g.toAlgebra
    let f := Algebra.ofId (MvPolynomial (Fin n) ℤ) (ZMod 4)
    IsRegular
      (Localization.AtPrime (graphPrime ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f p))
      ((List.finRange n).map
        (localDifference ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f p)) ∧
    RingHom.ker (localEvaluation ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f p) =
      Ideal.ofList ((List.finRange n).map
        (localDifference ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f p)) :=
  polynomial_localGraph ℤ (ZMod 4) n g p

/-- A disconnected source obeys the same literal graph-kernel statement. -/
theorem disconnected_localGraph (n : ℕ) (g : MvPolynomial (Fin n) ℚ →ₐ[ℚ] ℚ × ℚ)
    (p : Ideal (ℚ × ℚ)) [p.IsPrime] :
    letI := g.toAlgebra
    let f := Algebra.ofId (MvPolynomial (Fin n) ℚ) (ℚ × ℚ)
    IsRegular
      (Localization.AtPrime (graphPrime ℚ (Fin n) (ℚ × ℚ) (MvPolynomial (Fin n) ℚ) f p))
      ((List.finRange n).map
        (localDifference ℚ (Fin n) (ℚ × ℚ) (MvPolynomial (Fin n) ℚ) f p)) ∧
    RingHom.ker (localEvaluation ℚ (Fin n) (ℚ × ℚ) (MvPolynomial (Fin n) ℚ) f p) =
      Ideal.ofList ((List.finRange n).map
        (localDifference ℚ (Fin n) (ℚ × ℚ) (MvPolynomial (Fin n) ℚ) f p)) :=
  polynomial_localGraph ℚ (ℚ × ℚ) n g p

/-- The same original diagonal list acts weakly regularly on arbitrary graph coefficients. -/
theorem original_diagonalList_on_graph (R A : Type*)
    [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (g : MvPolynomial (Fin n) R →ₐ[R] A) (p : Ideal A) [p.IsPrime] :
    letI := g.toAlgebra
    let f := Algebra.ofId (MvPolynomial (Fin n) R) A
    letI := (localDiagonalPullback R (Fin n) A (MvPolynomial (Fin n) R) f p).toAlgebra
    IsWeaklyRegular
      (Localization.AtPrime (graphPrime R (Fin n) A (MvPolynomial (Fin n) R) f p))
      ((List.finRange n).map
        (RelativePolynomialTensor.localDifference R (Fin n) (MvPolynomial (Fin n) R)
          (p.comap (f : MvPolynomial (Fin n) R →+* A)))) := by
  let := g.toAlgebra
  exact isWeaklyRegular_diagonalList_on_graph R (Fin n) A (MvPolynomial (Fin n) R)
    (Algebra.ofId (MvPolynomial (Fin n) R) A) p (List.finRange n) (List.nodup_finRange n)

/-- The nonreduced example has an actual scheme graph stalk with its explicit regular kernel. -/
theorem nonreduced_scheme_graph (n : ℕ) (g : MvPolynomial (Fin n) ℤ →ₐ[ℤ] ZMod 4)
    (p : PrimeSpectrum (ZMod 4)) :
    letI := g.toAlgebra
    let f := Algebra.ofId (MvPolynomial (Fin n) ℤ) (ZMod 4)
    IsRegular
      ((AffineGraph.product ℤ (ZMod 4) (MvPolynomial (Fin n) ℤ)).presheaf.stalk
        (AffineGraph.graph ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f p))
      ((List.finRange n).map
        (AffineGraph.stalkDifference ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f p)) ∧
    RingHom.ker
      ((AffineGraph.graph ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f).stalkMap p).hom =
      Ideal.ofList ((List.finRange n).map
        (AffineGraph.stalkDifference ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ) f p)) := by
  let := g.toAlgebra
  exact AffineGraph.etale_stalkPresentation ℤ (Fin n) (ZMod 4) (MvPolynomial (Fin n) ℤ)
    (Algebra.ofId (MvPolynomial (Fin n) ℤ) (ZMod 4)) p (List.finRange n)
      (List.nodup_finRange n) List.mem_finRange

end Motivic.MotivicTest.EtaleGraph
