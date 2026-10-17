/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.LocalParameterDifferential
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # A local parameter differential comes from the original prime ideal -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential IsLocalRing
universe u v
namespace KaehlerDifferential

/-- Clearing the actual local parameter's denominator retains a nonzero residue
 differential and gives an element of the original prime ideal. -/
theorem exists_prime_residue_differential_ne_zero
    (k : Type u) (R : Type v) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ f ∈ p, (1 ⊗ₜ[R] D k R f :
      ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) ≠ 0 := by
  let A := Localization.AtPrime p
  let K := ResidueField A
  have : Algebra.EssFiniteType k A := .comp k R A
  have : Algebra.EssFiniteType k K := .comp k A K
  obtain ⟨f, hf, hdf⟩ := exists_maximalIdeal_residue_differential_ne_zero k A hpos
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq p.primeCompl f
  have ha : a ∈ p := (IsLocalization.AtPrime.mk'_mem_maximal_iff A p a s).mp (hs ▸ hf)
  refine ⟨a, ha, ?_⟩
  intro hz
  let L : K ⊗[R] Ω[R⁄k] →ₗ[K] K ⊗[A] Ω[A⁄k] :=
    (TensorProduct.mapOfCompatibleSMul A R K K Ω[A⁄k]).comp
      (AlgebraTensorModule.map (LinearMap.id : K →ₗ[K] K) (KaehlerDifferential.map k k R A))
  have hza : (1 ⊗ₜ[A] D k A (algebraMap R A a) : K ⊗[A] Ω[A⁄k]) = 0 := by
    have hh := congrArg L hz
    simpa only [L, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
      LinearMap.id_apply, TensorProduct.mapOfCompatibleSMul_tmul,
      KaehlerDifferential.map_D, map_zero] using hh
  have hae : algebraMap R A a = f * algebraMap R A s :=
    IsLocalization.mk'_eq_iff_eq_mul.mp hs
  have hf0 : algebraMap A K f = 0 := (residue_eq_zero_iff f).mpr hf
  have hsu : IsUnit (algebraMap R K s) :=
    (IsLocalization.map_units A s).map (algebraMap A K)
  rw [hae, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
    smul_tmul', smul_tmul', Algebra.smul_def, Algebra.smul_def,
    mul_one, mul_one, hf0, zero_tmul, zero_add] at hza
  have hs0 : algebraMap A K (algebraMap R A s) ≠ 0 := hsu.ne_zero
  have : (1 ⊗ₜ[A] D k A f : K ⊗[A] Ω[A⁄k]) = 0 := by
    apply (smul_eq_zero.mp ?_).resolve_left hs0
    simpa only [smul_tmul', smul_eq_mul, mul_one] using hza
  exact hdf this

end KaehlerDifferential
