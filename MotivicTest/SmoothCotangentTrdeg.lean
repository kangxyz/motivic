/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.SmoothCotangentTrdeg
public import Lean

/-! # Native smooth cotangent rank, including noninjective field-valued points -/
public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u
namespace MotivicTest.SmoothCotangentTrdeg

/-- No constant-rank or injectivity premise is hidden in the arbitrary field consumer. -/
theorem actual_field_fiber_rank
    (k R K : Type u) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra.Smooth k R] :
    Module.finrank K (K ⊗[R] Ω[R⁄k]) = (Algebra.trdeg k R).toNat ∧
      Algebra.trdeg k R < Cardinal.aleph0 :=
  ⟨Algebra.cotangent_finrank_eq_trdeg_toNat k R K, Algebra.smooth_trdeg_lt_aleph0 k R⟩

/-- Evaluation at the origin has a nonzero prime kernel; its fiber is still covered. -/
theorem origin_fiber_rank (k : Type u) [Field k] :
    letI : Algebra (MvPolynomial (Fin 1) k) k :=
      (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k))).toRingHom.toAlgebra
    Module.finrank k (k ⊗[MvPolynomial (Fin 1) k] Ω[MvPolynomial (Fin 1) k⁄k]) = 1 := by
  let : Algebra (MvPolynomial (Fin 1) k) k :=
    (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k))).toRingHom.toAlgebra
  change Module.finrank k (k ⊗[MvPolynomial (Fin 1) k] Ω[MvPolynomial (Fin 1) k⁄k]) = 1
  have ht : Algebra.trdeg k (MvPolynomial (Fin 1) k) = 1 := by
    simp
  rw [Algebra.cotangent_finrank_eq_trdeg_toNat k (MvPolynomial (Fin 1) k) k, ht]
  simp

open Lean in
run_cmd do
  for name in #[``actual_field_fiber_rank, ``origin_fiber_rank,
      ``Algebra.trdeg_eq_of_etale_localized_polynomial_map,
      ``Algebra.trdeg_eq_residue_cotangent_finrank,
      ``Algebra.cotangent_finrank_eq_trdeg_toNat] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Smooth cotangent rank with arbitrary field kernels: standard foundations only."

end MotivicTest.SmoothCotangentTrdeg
