/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.QuadraticFullSelectedPointOpen

/-! # Actual selected matrices evaluated at scalar-valued coefficients

These are identities for the original basis-coordinate matrices. They do not
assert an identification of cotangent modules after scalar extension.
-/

@[expose] public noncomputable section

open Module _root_.MvPolynomial

namespace QuadraticIncidence

universe u

variable {κ K σ V : Type u} [Field κ] [Field K] [Fintype σ]
  [AddCommGroup V] [Module κ V]

/-- The full determinant evaluates to the actual mapped original coefficient matrix. -/
theorem eval₂_fullSelectedDeterminant
    (φ : κ →+* K) (d : ℕ) (B : Basis (Fin d) κ V)
    (J : restrictTotalDegree σ κ 2 →ₗ[κ] V) (c : Fin d × Exponent σ → K) :
    eval₂ φ c (fullSelectedDeterminant d B J) =
      Matrix.det (fun i j : Fin d =>
        ∑ q, φ (B.repr (J (parameterBasis κ σ d q i)) j) * c q) := by
  classical
  change (eval₂Hom φ c) (fullSelectedMatrix d B J).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [fullSelectedMatrix]

/-- The chosen d-row minor evaluates in precisely the same original coordinates. -/
theorem eval₂_selectedDeterminant
    (φ : κ →+* K) (d : ℕ) (B : Basis (Fin (d + 1)) κ V)
    (J : restrictTotalDegree σ κ 2 →ₗ[κ] V) (c : Fin d × Exponent σ → K) :
    eval₂ φ c (selectedDeterminant d B J) =
      Matrix.det (fun i j : Fin d =>
        ∑ q, φ (B.repr (J (parameterBasis κ σ d q i)) j.castSucc) * c q) := by
  classical
  change (eval₂Hom φ c) (selectedMatrix d B J).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [selectedMatrix]

end QuadraticIncidence
