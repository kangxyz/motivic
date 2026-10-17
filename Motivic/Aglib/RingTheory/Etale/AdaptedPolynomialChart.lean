/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.PrescribedLocalBasis
public import Motivic.Aglib.RingTheory.Etale.PolynomialDifferentialBasis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.Etale

/-! # Adapted polynomial coordinates retaining a regular equation -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Module TensorProduct KaehlerDifferential

universe u v

namespace Algebra

/-- A differential basis at a prime selected from the original affine ring,
containing the unchanged regular equation. -/
theorem exists_localized_differential_basis_containing
    (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Algebra k R]
    [Smooth k R] (t : R) (ht : IsRegular t)
    [FormallySmooth k (R ⧸ Ideal.span {t})]
    (p : Ideal R) [p.IsPrime] (htp : t ∈ p) :
    ∃ (s : Set R), t ∈ s ∧ s.Finite ∧
      ∃ b : Basis s (Localization.AtPrime p)
        ((Localization.AtPrime p) ⊗[R] Ω[R⁄k]), ∀ j, b j = 1 ⊗ₜ D k R j := by
  let Rp := Localization.AtPrime p
  let K := IsLocalRing.ResidueField Rp
  let M := Rp ⊗[R] Ω[R⁄k]
  let v : R → M := fun x ↦ 1 ⊗ₜ D k R x
  have hv : Submodule.span Rp (Set.range v) = ⊤ := by
    have h := congrArg (Submodule.baseChange Rp) (span_range_derivation k R)
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top,
      ← Set.range_comp, Function.comp_def, TensorProduct.mk_apply, v] using h
  have htK : algebraMap R K t = 0 := by
    rw [IsScalarTower.algebraMap_apply R Rp K]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p t).mpr htp)
  have hn : (1 ⊗ₜ[Rp] v t : K ⊗[Rp] M) ≠ 0 := by
    intro h
    have hh := congrArg (AlgebraTensorModule.cancelBaseChange R Rp K K Ω[R⁄k]) h
    have hnon := FormallySmooth.tensor_differential_ne_zero_of_regular_quotient k R t ht K htK
    apply hnon
    change (1 : Rp) • (1 : K) ⊗ₜ[R] D k R t = 0 at hh
    simpa only [one_smul] using hh
  obtain ⟨s, hs, b, hb⟩ := IsLocalRing.exists_basis_subfamily_containing Rp M v hv t hn
  have : Finite s := Module.Finite.finite_basis b
  exact ⟨s, hs, Set.toFinite s, b, hb⟩

/-- Near every prime on a smooth regular principal divisor there is an actual
étale polynomial chart having the unchanged divisor equation as a coordinate.
The coefficients are taken from the original ring and only one principal open
is removed. No rationality, separability, perfectness, or infinitude is assumed. -/
theorem exists_etale_polynomial_chart_preserving_regular_generator
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [Smooth k R] (t : R) (ht : IsRegular t)
    [FormallySmooth k (R ⧸ Ideal.span {t})]
    (p : Ideal R) [p.IsPrime] (htp : t ∈ p) :
    ∃ (s : Set R), t ∈ s ∧ s.Finite ∧ ∃ r ∉ p,
      ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R))).toRingHom).Etale := by
  classical
  obtain ⟨s, hts, hs, b, hb⟩ :=
    exists_localized_differential_basis_containing k R t ht p htp
  let : Fintype s := hs.fintype
  let P := MvPolynomial s k
  let f : P →ₐ[k] R := MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R))
  let : Algebra P R := f.toRingHom.toAlgebra
  have : IsScalarTower k P R := .of_algebraMap_eq' f.comp_algebraMap.symm
  let Rp := Localization.AtPrime p
  let e := tensorKaehlerEquivOfFormallyEtale k R Rp
  let bR := b.map e
  have hbR (j : s) : bR j = D k Rp (algebraMap P Rp (.X j)) := by
    change e (b j) = _
    rw [hb]
    change mapBaseChange k R Rp (1 ⊗ₜ D k R (j : R)) = _
    rw [mapBaseChange_tmul, one_smul, map_D]
    congr 1
    rw [IsScalarTower.algebraMap_apply P R Rp]
    change (algebraMap R Rp) (j : R) = (algebraMap R Rp)
      ((MvPolynomial.aeval (R := k) (fun j : s ↦ (j : R))) (.X j))
    exact congrArg (algebraMap R Rp) (MvPolynomial.aeval_X (R := k)
      (fun j : s ↦ (j : R)) j).symm
  have : FormallyEtale P Rp :=
    FormallyEtale.of_polynomial_differential_basis k Rp s bR hbR
  have : FiniteType P R := FiniteType.of_restrictScalars_finiteType k P R
  have : FinitePresentation P R := FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨r, hr, he⟩ := exists_etale_of_isEtaleAt (R := P) p
  refine ⟨s, hts, hs, r, hr, ?_⟩
  have h := (RingHom.etale_algebraMap (R := P) (S := Localization.Away r)).mpr he
  convert h using 1

end Algebra
