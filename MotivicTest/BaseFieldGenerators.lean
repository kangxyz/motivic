/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseFieldGenerators
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual base-field correspondence classification

These checks retain arbitrary fields, signed integer coefficients, and the
literal smooth-site base and categorical identity. They also verify that
postcomposition sends every base-field cycle to the same integer multiple
of the postcomposing correspondence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.BaseFieldGenerators

variable {k : Type u} [Field k]

/-- Actual integral closed supports over a field have a single possible generator. -/
theorem actual_generator (A : FiniteCorrespondenceGenerator
    (𝟙 (Spec (.of k))) (𝟙 (Spec (.of k)))) :
    A = identityGenerator (𝟙 (Spec (.of k))) :=
  A.eq_identityGenerator_of_base

/-- Typeclass consumers can use the uniqueness of literal geometric supports. -/
theorem actual_generator_subsingleton : Subsingleton (FiniteCorrespondenceGenerator
    (𝟙 (Spec (.of k))) (𝟙 (Spec (.of k)))) := inferInstance

/-- The classification is into all integers, including negative multiplicities. -/
theorem actual_signed_cycle
    (α : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.base (Spec (.of k)))) :
    ∃! n : ℤ, α = n • 𝟙 (Cor.mk (SmoothSite.base (Spec (.of k)))) :=
  Cor.base_endomorphism_existsUnique_zsmul_id α

/-- The actual classification reduces arbitrary postcomposition to the identity axis. -/
theorem actual_postcomposition {Y : Cor k}
    (α : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.base (Spec (.of k))))
    (β : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶ Y) :
    ∃ n : ℤ, α ≫ β = n • β := by
  obtain ⟨n, hn, _⟩ := Cor.base_endomorphism_existsUnique_zsmul_id α
  refine ⟨n, ?_⟩
  rw [hn, Preadditive.zsmul_comp, Category.id_comp]

end MotivicTest.BaseFieldGenerators

open Lean in
run_cmd do
  for name in #[
      `Motivic.FiniteCorrespondenceGenerator.eq_identityGenerator_of_base,
      `Motivic.FiniteCorrespondenceGenerator.baseGeneratorSubsingleton,
      `Motivic.FiniteCorrespondence.eq_coefficient_zsmul_identity_cycle,
      `Motivic.Cor.base_id_eq_identityGenerator_cycle,
      `Motivic.Cor.base_endomorphism_eq_coefficient_zsmul_id,
      `Motivic.Cor.base_endomorphism_existsUnique_zsmul_id,
      `MotivicTest.BaseFieldGenerators.actual_generator,
      `MotivicTest.BaseFieldGenerators.actual_generator_subsingleton,
      `MotivicTest.BaseFieldGenerators.actual_signed_cycle,
      `MotivicTest.BaseFieldGenerators.actual_postcomposition] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual base-field generators and consumers use only standard Lean foundations."
