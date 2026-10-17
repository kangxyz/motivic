/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.ResidueCotangentTrdeg
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Smooth cotangent fiber rank equals the native transcendence degree

The residue rank determines an actual localized étale polynomial chart.
Localization is algebraic and injective, so its transcendence degree is the
original domain's transcendence degree, not merely an upper bound.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u
namespace Algebra

/-- A nonempty localized étale chart determines the original domain's exact trdeg. -/
theorem trdeg_eq_of_etale_localized_polynomial_map
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] R) {r : R} (hr : r ≠ 0)
    (hf : ((algebraMap R (Localization.Away r)).comp f.toRingHom).Etale) :
    Algebra.trdeg k R = n := by
  let L := Localization.Away r
  have : IsDomain L := Localization.Away.isDomain hr
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr
    (IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hr))
  have : Algebra.IsAlgebraic R L := IsLocalization.isAlgebraic L (Submonoid.powers r)
  have hdeg : Algebra.trdeg k L = n :=
    trdeg_eq_of_etale_polynomial_map ((IsScalarTower.toAlgHom k R L).comp f) hf
  have ht := trdeg_add_eq k R (A := L)
  rw [trdeg_eq_zero (R := R) (A := L), add_zero] at ht
  exact ht.trans hdeg

/-- The native cardinal transcendence degree equals the actual residue cotangent rank. -/
theorem trdeg_eq_residue_cotangent_finrank
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] :
    Algebra.trdeg k R =
      (Module.finrank p.ResidueField (p.ResidueField ⊗[R] Ω[R⁄k]) : Cardinal) := by
  let n := Module.finrank p.ResidueField (p.ResidueField ⊗[R] Ω[R⁄k])
  obtain ⟨g, b, hb⟩ := exists_residue_basis_fin_original_functions k R p.ResidueField n rfl
  obtain ⟨r, hr, he⟩ := exists_etale_polynomial_map_of_residue_differential_basis k R p g b hb
  have hr0 : r ≠ 0 := fun h => hr (h.symm ▸ p.zero_mem)
  exact trdeg_eq_of_etale_localized_polynomial_map (MvPolynomial.aeval g) hr0 he

/-- In particular the prime-residue cotangent dimension is exactly the finite trdeg. -/
theorem residue_cotangent_finrank_eq_trdeg_toNat
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] Ω[R⁄k]) =
      (Algebra.trdeg k R).toNat := by
  rw [trdeg_eq_residue_cotangent_finrank k R p, Cardinal.toNat_natCast]

/-- The arbitrary field-valued cotangent fiber has the same dimension, including
when the structural map has a nonzero moving prime kernel. -/
theorem cotangent_finrank_eq_trdeg_toNat
    (k R K : Type u) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Smooth k R] :
    Module.finrank K (K ⊗[R] Ω[R⁄k]) = (Algebra.trdeg k R).toNat := by
  let p := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime (algebraMap R K)
  have hu : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) := by
    intro r hr
    exact isUnit_iff_ne_zero.mpr hr
  let f : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap R K) le_rfl hu
  let : Algebra p.ResidueField K := f.toAlgebra
  have : IsScalarTower R p.ResidueField K := .of_algebraMap_eq' (by
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p (algebraMap R K) le_rfl hu r).symm)
  let e := AlgebraTensorModule.cancelBaseChange R p.ResidueField K K Ω[R⁄k]
  calc
    Module.finrank K (K ⊗[R] Ω[R⁄k]) =
        Module.finrank K (K ⊗[p.ResidueField] (p.ResidueField ⊗[R] Ω[R⁄k])) :=
      e.finrank_eq.symm
    _ = Module.finrank p.ResidueField (p.ResidueField ⊗[R] Ω[R⁄k]) :=
      Module.finrank_baseChange
    _ = (Algebra.trdeg k R).toNat := residue_cotangent_finrank_eq_trdeg_toNat k R p

/-- The native transcendence degree here is genuinely finite. -/
theorem smooth_trdeg_lt_aleph0
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Smooth k R] :
    Algebra.trdeg k R < Cardinal.aleph0 :=
  trdeg_lt_aleph0_of_finiteType

end Algebra
