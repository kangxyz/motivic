/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.Length

/-!
# Finite-length Euler characteristics of actual homology

The coefficients here are module lengths over the given ring. They are not
vector-space ranks. Every integer length requires a proof that the module has
finite length; every Euler characteristic requires finite support as well.
The complexes and their homology are mathlib's categorical constructions.
We prove invariance under actual quasi-isomorphisms, with both natural chain
and integer cochain sign conventions available.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace HomologicalComplex.ModuleLengthEuler

variable {R : Type u} [Ring R]

/-- Integer-valued module length, with infinite length excluded by its input. -/
noncomputable def integerLength (M : Type v) [AddCommGroup M] [Module R M]
    (_h : Module.length R M ≠ ⊤) : ℤ :=
  (Module.length R M).toNat

/-- Isomorphic finite-length modules have the same integer length. -/
theorem integerLength_eq_of_equiv {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : Module.length R M ≠ ⊤) (hN : Module.length R N ≠ ⊤) :
    integerLength M hM = integerLength N hN := by
  simp only [integerLength, e.length_eq]

variable {ι : Type w}

/-- All modules have finite length, and only finitely many have nonzero length.
Equivalently, the graded module is zero outside finitely many degrees. -/
structure FiniteLengthSupport (X : ι → ModuleCat.{v} R) : Prop where
  /-- No infinite module length is converted to an integer. -/
  finite_length : ∀ i, Module.length R (X i) ≠ ⊤
  /-- Actual nonzero module lengths have finite support. -/
  finite_support : (Function.support fun i => Module.length R (X i)).Finite

/-- Finite length on a finite set and zero modules outside it suffice. -/
theorem FiniteLengthSupport.of_isZero_outside (X : ι → ModuleCat.{v} R)
    (s : Finset ι) (hfin : ∀ i ∈ s, Module.length R (X i) ≠ ⊤)
    (hzero : ∀ i ∉ s, CategoryTheory.Limits.IsZero (X i)) : FiniteLengthSupport X where
  finite_length i := by
    by_cases hi : i ∈ s
    · exact hfin i hi
    · have : Subsingleton (X i) := ModuleCat.isZero_iff_subsingleton.mp (hzero i hi)
      simp
  finite_support := s.finite_toSet.subset fun i hi => by
    by_contra his
    have : Subsingleton (X i) := ModuleCat.isZero_iff_subsingleton.mp (hzero i his)
    exact hi Module.length_eq_zero

/-- Finite-length support is preserved by degreewise module isomorphisms. -/
theorem FiniteLengthSupport.of_iso {X Y : ι → ModuleCat.{v} R}
    (h : FiniteLengthSupport X) (e : ∀ i, X i ≅ Y i) : FiniteLengthSupport Y where
  finite_length i := by rw [← (e i).toLinearEquiv.length_eq]; exact h.finite_length i
  finite_support := by
    have he : (fun i => Module.length R (Y i)) = fun i => Module.length R (X i) := by
      funext i
      exact (e i).toLinearEquiv.length_eq.symm
    rw [he]
    exact h.finite_support

/-- Injective reindexing preserves finite-length support. -/
theorem FiniteLengthSupport.comp {κ : Type*} {X : ι → ModuleCat.{v} R}
    (h : FiniteLengthSupport X) (f : κ → ι) (hf : Function.Injective f) :
    FiniteLengthSupport (fun i => X (f i)) where
  finite_length i := h.finite_length (f i)
  finite_support := Function.HasFiniteSupport.fun_comp_of_injective hf h.finite_support

/-- The finite signed length sum of a graded module. The evidence excludes
both infinite-length and infinite-support default values. -/
noncomputable def signedLengthSum (X : ι → ModuleCat.{v} R) (sign : ι → ℤ)
    (h : FiniteLengthSupport X) : ℤ :=
  ∑ᶠ i, sign i * integerLength (X i) (h.finite_length i)

/-- The signed summand really has finite support. -/
theorem finiteSupport_summand (X : ι → ModuleCat.{v} R) (sign : ι → ℤ)
    (h : FiniteLengthSupport X) :
    (fun i => sign i * integerLength (X i) (h.finite_length i)).HasFiniteSupport := by
  apply h.finite_support.subset
  intro i hi
  contrapose! hi
  simp only [Function.mem_support, not_not] at hi ⊢
  simp [integerLength, hi]

/-- The Euler sum can be computed over any finite set containing the actual
nonzero degrees, so its value does not depend on a chosen bound. -/
theorem signedLengthSum_eq_sum (X : ι → ModuleCat.{v} R) (sign : ι → ℤ)
    (h : FiniteLengthSupport X) (s : Finset ι)
    (hs : Function.support (fun i => Module.length R (X i)) ⊆ s) :
    signedLengthSum X sign h = ∑ i ∈ s, sign i * integerLength (X i) (h.finite_length i) := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hs
  contrapose! hi
  simp only [Function.mem_support, not_not] at hi ⊢
  simp [integerLength, hi]

/-- Degreewise isomorphisms preserve signed length sums. -/
theorem signedLengthSum_eq_of_iso {X Y : ι → ModuleCat.{v} R} (sign : ι → ℤ)
    (hX : FiniteLengthSupport X) (hY : FiniteLengthSupport Y) (e : ∀ i, X i ≅ Y i) :
    signedLengthSum X sign hX = signedLengthSum Y sign hY := by
  apply finsum_congr
  intro i
  rw [integerLength_eq_of_equiv (e i).toLinearEquiv]

variable {c : ComplexShape ι}

/-- A homological complex has finite-length homology in finitely many degrees. -/
abbrev FiniteHomology (K : HomologicalComplex (ModuleCat.{v} R) c) : Prop :=
  FiniteLengthSupport (fun i => K.homology i)

/-- Signed Euler characteristic of the actual categorical homology. -/
noncomputable def homologyEuler (K : HomologicalComplex (ModuleCat.{v} R) c)
    (sign : ι → ℤ) (h : FiniteHomology K) : ℤ :=
  signedLengthSum (fun i => K.homology i) sign h

/-- A quasi-isomorphism transports genuine finite-length homology support. -/
theorem FiniteHomology.of_quasiIso {K L : HomologicalComplex (ModuleCat.{v} R) c}
    (h : FiniteHomology K) (f : K ⟶ L) [QuasiIso f] : FiniteHomology L :=
  h.of_iso (fun i => isoOfQuasiIsoAt f i)

/-- Genuine homology length Euler characteristics are quasi-isomorphism invariant. -/
theorem homologyEuler_eq_of_quasiIso {K L : HomologicalComplex (ModuleCat.{v} R) c}
    (f : K ⟶ L) [QuasiIso f] (sign : ι → ℤ)
    (hK : FiniteHomology K) (hL : FiniteHomology L) :
    homologyEuler K sign hK = homologyEuler L sign hL :=
  signedLengthSum_eq_of_iso sign hK hL (fun i => isoOfQuasiIsoAt f i)

/-- Euler characteristic for a natural-number chain complex, with sign `(-1)^i`. -/
noncomputable abbrev chainEuler (K : ChainComplex (ModuleCat.{v} R) ℕ)
    (h : FiniteHomology K) : ℤ :=
  homologyEuler K (fun i => (-1) ^ i) h

/-- Euler characteristic for an integer cochain complex, with sign `(-1)^i`. -/
noncomputable abbrev cochainEuler (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (h : FiniteHomology K) : ℤ :=
  homologyEuler K (fun i => (i.negOnePow : ℤ)) h

end HomologicalComplex.ModuleLengthEuler
