/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The two-element Koszul complex and local intersection multiplicities

This module constructs the literal complex `M → M × M → M` for two scalars,
its three homology modules, and its finite-length Euler multiplicity. In
particular it keeps the positive-degree homology corrections; a scheme-theoretic
fibre length alone is not the general intersection multiplicity.

The regular-sequence theorem proves vanishing of both higher homology modules.
This is the local algebra needed when a codimension-two intersection is computed
by a regular sequence on the intersected module. It is not a construction of
finite-correspondence composition or a proof that arbitrary such intersections
are Tor-independent.

The definitions and proofs here are independent Mathlib-based code. The
mathematical convention follows MVW, Appendix 17A.1, where intersection
multiplicity is the alternating sum of local Tor lengths.
-/

@[expose] public section

universe u v

namespace Motivic.LocalLength.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (a b : R)

/-- The degree-one Koszul differential `(x,y) ↦ a • x + b • y`. -/
def d₁ : (M × M) →ₗ[R] M :=
  (LinearMap.lsmul R M a).comp (LinearMap.fst R M M) +
    (LinearMap.lsmul R M b).comp (LinearMap.snd R M M)

/-- The degree-two Koszul differential `z ↦ (-b • z, a • z)`. -/
def d₂ : M →ₗ[R] (M × M) :=
  (-LinearMap.lsmul R M b).prod (LinearMap.lsmul R M a)

@[simp]
theorem d₁_apply (x : M × M) : d₁ M a b x = a • x.1 + b • x.2 := rfl

@[simp]
theorem d₂_apply (x : M) : d₂ M a b x = (-(b • x), a • x) := rfl

theorem d₁_d₂ (x : M) : d₁ M a b (d₂ M a b x) = 0 := by
  simp only [d₁_apply, d₂_apply, smul_neg]
  rw [smul_smul, smul_smul, mul_comm a b, neg_add_cancel]

/-- The degree-one cycles of the actual two-element Koszul complex. -/
abbrev Cycles : Submodule R (M × M) := LinearMap.ker (d₁ M a b)

/-- The degree-two differential with codomain restricted to cycles. -/
def toCycles : M →ₗ[R] Cycles M a b :=
  (d₂ M a b).codRestrict (Cycles M a b) (d₁_d₂ M a b)

/-- Degree-zero Koszul homology. -/
abbrev H₀ := M ⧸ LinearMap.range (d₁ M a b)

/-- Degree-one Koszul homology, with the actual boundary submodule. -/
abbrev H₁ := Cycles M a b ⧸ LinearMap.range (toCycles M a b)

/-- Degree-two Koszul homology. -/
abbrev H₂ := LinearMap.ker (d₂ M a b)

/-- The quotient by the first scalar, used to state regularity of the pair. -/
abbrev PrincipalQuotient := M ⧸ LinearMap.range (LinearMap.lsmul R M a)

/-- The two-element Koszul sequence is exact in degree one for a regular pair.
Neither the ring nor the module is assumed to have finite length. -/
theorem exact_of_regular (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b) :
    Function.Exact (d₂ M a b) (d₁ M a b) := by
  intro x
  constructor
  · intro hx
    change a • x.1 + b • x.2 = 0 at hx
    have hy : (Submodule.Quotient.mk x.2 : PrincipalQuotient M a) = 0 := by
      apply hb
      simp only [smul_zero]
      change (Submodule.Quotient.mk (b • x.2) : PrincipalQuotient M a) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨-x.1, ?_⟩
      change a • (-x.1) = b • x.2
      have h := (neg_eq_iff_add_eq_zero).mpr hx
      simpa only [d₁_apply, smul_neg] using h
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    refine ⟨z, Prod.ext ?_ hz⟩
    apply ha
    change a • (-(b • z)) = a • x.1
    have hx' : a • x.1 + b • (a • z) = 0 := by
      simpa only [d₁_apply, ← hz, LinearMap.lsmul_apply] using hx
    rw [smul_neg, smul_smul, mul_comm a b, ← smul_smul]
    exact (neg_eq_iff_add_eq_zero).mpr (by simpa only [add_comm] using hx')
  · rintro ⟨z, rfl⟩
    exact d₁_d₂ M a b z

/-- The left Koszul differential is injective when its first scalar is regular. -/
theorem d₂_injective_of_regular (ha : IsSMulRegular M a) :
    Function.Injective (d₂ M a b) := by
  intro x y h
  exact ha (congrArg Prod.snd h)

/-- A regular pair has no degree-one Koszul homology. -/
theorem subsingleton_H₁_of_regular (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b) :
    Subsingleton (H₁ M a b) := by
  have hs : Function.Surjective (toCycles M a b) := by
    intro x
    obtain ⟨z, hz⟩ := (exact_of_regular M a b ha hb x).mp x.property
    exact ⟨z, Subtype.ext hz⟩
  have ht : LinearMap.range (toCycles M a b) = ⊤ := LinearMap.range_eq_top.mpr hs
  rw [H₁, ht]
  infer_instance

/-- A regular first scalar already kills degree-two Koszul homology. -/
theorem subsingleton_H₂_of_regular (ha : IsSMulRegular M a) :
    Subsingleton (H₂ M a b) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  exact d₂_injective_of_regular M a b ha (x.property.trans y.property.symm)

end Motivic.LocalLength.KoszulPair
