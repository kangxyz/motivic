/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PrincipalFamilyEndpointKernel
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regularity of the original face scalar on both principal terms

The actual integral endpoint makes its scalar ideal prime. A nonzero original
endpoint image then gives regularity on the complete numerator or denominator
quotient by prime cancellation. Native minimal-prime avoidance gives regularity
on every reduced component quotient as well. Only the ambient polynomial
projection is flat, as a base change from a field; no closed support is assumed
flat. Identifying these local minimal primes with the original scheme component
stalks remains a separate geometric comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

/-- Prime cancellation on the full principal quotient, without factoriality. -/
private theorem scalar_regular_quotient_of_prime
    {R : Type u} [CommRing R] (c n : R) (hc : IsSMulRegular R c)
    (hp : (Ideal.span {c} : Ideal R).IsPrime) (hn : n ∉ (Ideal.span {c} : Ideal R)) :
    IsSMulRegular (R ⧸ Ideal.span {n}) c := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {n}) c).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  have hny : n * y ∈ (Ideal.span {c} : Ideal R) := by
    rw [← hy]
    exact Ideal.mem_span_singleton.mpr ⟨x, rfl⟩
  have hyc : y ∈ (Ideal.span {c} : Ideal R) := (hp.mem_or_mem hny).resolve_left hn
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hyc
  have he : c • x = c • (n * z) := by
    change c * x = c * (n * z)
    calc
      c * x = n * y := hy
      _ = c * (n * z) := by rw [hz]; ring
  exact Ideal.mem_span_singleton.mpr ⟨z, hc he⟩

/-- The original scalar avoids every minimal prime of the full principal term. -/
private theorem scalar_regular_minimal_quotients
    {R : Type u} [CommRing R] (c n : R)
    (h : IsSMulRegular (R ⧸ Ideal.span {n}) c) :
    ∀ Q : Ideal R, Q ∈ (Ideal.span {n}).minimalPrimes → IsSMulRegular (R ⧸ Q) c := by
  intro Q hQ
  have hnot : c ∉ Q := h.notMem_of_mem_minimalPrimes (by
    simpa only [Ideal.annihilator_quotient] using hQ)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem Q c).mpr
  intro x hx
  exact (hQ.1.1.mem_or_mem hx).resolve_left hnot

variable {k : Type u} [Field k] {W : Scheme.{u}} [IsIntegral W]
  (p : W ⟶ Spec (.of k))

/-- A nonzero image under the actual endpoint stalk map gives regularity on
both the whole principal quotient and all its local minimal-component quotients. -/
theorem endpoint_scalar_regular_on_principal_term
    (c : k) (x : W) (s : Γ(parameterSpace p, ⊤))
    (hs : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) ≠ 0) :
    let R := (parameterSpace p).presheaf.stalk (endpoint p c x)
    let n := (parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s
    let t := FiniteFlatCurve.scalar (parameterProjection p) c (endpoint p c x)
    IsSMulRegular (R ⧸ Ideal.span {n}) t ∧
      ∀ Q : Ideal R, Q ∈ (Ideal.span {n}).minimalPrimes → IsSMulRegular (R ⧸ Q) t := by
  dsimp only
  let R := (parameterSpace p).presheaf.stalk (endpoint p c x)
  let n : R := (parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s
  let t : R := FiniteFlatCurve.scalar (parameterProjection p) c (endpoint p c x)
  have hp : (Ideal.span {t} : Ideal R).IsPrime := by
    rw [← endpoint_stalk_kernel p c x]
    exact RingHom.ker_isPrime ((endpoint p c).stalkMap x).hom
  have hn : n ∉ (Ideal.span {t} : Ideal R) := by
    rw [← endpoint_stalk_kernel p c x, RingHom.mem_ker]
    change (endpoint p c).stalkMap x
      ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s) ≠ 0
    rwa [endpoint_germ]
  have : Flat (parameterProjection p) := MorphismProperty.pullback_snd _ _ inferInstance
  have ht : IsSMulRegular R t :=
    FiniteFlatCurve.scalar_regular (parameterProjection p) c (endpoint p c x)
  have h := scalar_regular_quotient_of_prime t n ht hp hn
  exact ⟨h, scalar_regular_minimal_quotients t n h⟩

/-- For the literal numerator and denominator, the checked zero/one evaluations
supply nonvanishing, so component regularity is derived rather than assumed. -/
theorem numerator_denominator_endpoint_regularity
    (a b : Γ(W, ⊤)) (x : W)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (c : k) (hc : c = 0 ∨ c = 1)
    (s : Γ(parameterSpace p, ⊤)) (hs : s = numerator p a b ∨ s = denominator p b) :
    let R := (parameterSpace p).presheaf.stalk (endpoint p c x)
    let n := (parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s
    let t := FiniteFlatCurve.scalar (parameterProjection p) c (endpoint p c x)
    IsSMulRegular (R ⧸ Ideal.span {n}) t ∧
      ∀ Q : Ideal R, Q ∈ (Ideal.span {n}).minimalPrimes → IsSMulRegular (R ⧸ Q) t := by
  apply endpoint_scalar_regular_on_principal_term p c x s
  rcases hs with rfl | rfl
  · rcases hc with rfl | rfl
    · simpa only [numerator_zero] using hb
    · simpa only [numerator_one] using ha
  · simpa only [denominator_endpoint] using hb

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
