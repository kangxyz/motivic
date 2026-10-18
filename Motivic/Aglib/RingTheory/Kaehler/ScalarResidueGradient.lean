/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.ScalarResidueCotangent
public import Motivic.Aglib.RingTheory.Kaehler.ResidueGeneratorGradient

/-! # Original generator gradients in the scalar-extended cotangent fiber -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace KaehlerDifferential

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k R L K : Type u) [CommRing k] [CommRing R] [CommRing L] [CommRing K]
  [Algebra k R] [Algebra k L] [Algebra (R ⊗[k] L) K]
  [Algebra R K] [IsScalarTower R (R ⊗[k] L) K]
  {σ : Type u} [Fintype σ]

/-- The original gradient coefficients are unchanged by the cotangent equivalence. -/
theorem scalarResidueEquiv_gradient (g : σ → R) (c : σ → K) :
    scalarResidueEquiv k R L K (residueGeneratorGradient k R K g c) =
      residueGeneratorGradient L (R ⊗[k] L) K
        (algebraMap R (R ⊗[k] L) ∘ g) c := by
  simp only [residueGeneratorGradient, Fintype.linearCombination_apply, map_sum, map_smul,
    scalarResidueEquiv_tmul_D, Function.comp_apply]

/-- Actual scalar-source cotangent independence follows from the original
field-valued gradient calculation, not from an assumed geometric identification. -/
theorem independent_scalarResidueGradient {ι : Type v}
    (g : σ → R) (c : ι → σ → K)
    (h : LinearIndependent K (fun i => residueGeneratorGradient k R K g (c i))) :
    LinearIndependent K (fun i => residueGeneratorGradient L (R ⊗[k] L) K
      (algebraMap R (R ⊗[k] L) ∘ g) (c i)) := by
  have h' := h.map' (scalarResidueEquiv k R L K).toLinearMap
    (LinearMap.ker_eq_bot.mpr (scalarResidueEquiv k R L K).injective)
  simpa only [Function.comp_def, LinearEquiv.coe_coe, scalarResidueEquiv_gradient] using h'

end KaehlerDifferential
