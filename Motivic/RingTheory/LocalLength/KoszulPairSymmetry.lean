/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.KoszulPair

/-!
# Interchanging two local Koszul equations

The swap of the two degree-one coordinates, together with negation in degree
two, induces actual linear equivalences on the three Koszul homology modules.
Consequently the finite-length Euler multiplicity is symmetric in the two
equations, including the nonregular case. This proves a local permutation law;
it is not the full associativity or projection formula for correspondence cycles.
-/

@[expose] public section

universe u v

namespace Motivic.LocalLength.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

/-- Exchanging the equations exchanges the coordinates of every one-cycle. -/
def cyclesSwap : Cycles M a b ≃ₗ[R] Cycles M b a where
  toFun x := ⟨(x.1.2, x.1.1), by
    change b • x.1.2 + a • x.1.1 = 0
    have hx : a • x.1.1 + b • x.1.2 = 0 := x.property
    simpa only [add_comm] using hx⟩
  invFun x := ⟨(x.1.2, x.1.1), by
    change a • x.1.2 + b • x.1.1 = 0
    have hx : b • x.1.1 + a • x.1.2 = 0 := x.property
    simpa only [add_comm] using hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The sign in degree two is forced by the actual Koszul differential. -/
theorem cyclesSwap_toCycles :
    (cyclesSwap M a b).toLinearMap.comp (toCycles M a b) = -(toCycles M b a) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (a • x, -(b • x)) = (-(-(a • x)), -(b • x))
  rw [neg_neg]

/-- Zeroth homology is invariant under exchanging the two equations. -/
noncomputable def homologyZeroSwap : H₀ M a b ≃ₗ[R] H₀ M b a :=
  Submodule.quotEquivOfEq _ _ (by
    ext x
    constructor
    · rintro ⟨⟨y, z⟩, rfl⟩
      exact ⟨(z, y), add_comm _ _⟩
    · rintro ⟨⟨y, z⟩, rfl⟩
      exact ⟨(z, y), add_comm _ _⟩)

/-- The coordinate swap gives the actual equivalence on first homology. -/
noncomputable def homologyOneSwap : H₁ M a b ≃ₗ[R] H₁ M b a :=
  Submodule.Quotient.equiv _ _ (cyclesSwap M a b) (by
    rw [← LinearMap.range_comp, cyclesSwap_toCycles, LinearMap.range_neg])

/-- The top homology consists of elements killed by both scalars. -/
theorem mem_H₂_iff (x : M) : x ∈ H₂ M a b ↔ a • x = 0 ∧ b • x = 0 := by
  change (-(b • x), a • x) = (0, 0) ↔ _
  simp only [Prod.mk.injEq, neg_eq_zero, and_comm]

/-- Second homology is invariant under exchanging the equations. -/
noncomputable def homologyTwoSwap : H₂ M a b ≃ₗ[R] H₂ M b a :=
  LinearEquiv.ofEq _ _ (by
    ext x
    simp only [mem_H₂_iff, and_comm])

/-- Exactly the finiteness required to interpret the three lengths as integers. -/
def HasFiniteHomology : Prop :=
  Module.length R (H₀ M a b) ≠ ⊤ ∧ Module.length R (H₁ M a b) ≠ ⊤ ∧
    Module.length R (H₂ M a b) ≠ ⊤

/-- The finite-length Euler multiplicity, with both higher-homology corrections. -/
noncomputable def eulerMultiplicity (_h : HasFiniteHomology M a b) : ℤ :=
  ((Module.length R (H₀ M a b)).toNat : ℤ) -
    ((Module.length R (H₁ M a b)).toNat : ℤ) +
    ((Module.length R (H₂ M a b)).toNat : ℤ)

/-- Finite homology is preserved by swapping the equations. -/
theorem hasFiniteHomology_swap : HasFiniteHomology M a b ↔ HasFiniteHomology M b a := by
  unfold HasFiniteHomology
  rw [(homologyZeroSwap M a b).length_eq, (homologyOneSwap M a b).length_eq,
    (homologyTwoSwap M a b).length_eq]

/-- The full two-equation Euler multiplicity is symmetric, with no regularity premise. -/
theorem eulerMultiplicity_swap (h : HasFiniteHomology M a b) :
    eulerMultiplicity M a b h =
      eulerMultiplicity M b a ((hasFiniteHomology_swap M a b).mp h) := by
  unfold eulerMultiplicity
  rw [(homologyZeroSwap M a b).length_eq, (homologyOneSwap M a b).length_eq,
    (homologyTwoSwap M a b).length_eq]

/-- A regular pair has finite Koszul homology as soon as the ordinary quotient does. -/
theorem hasFiniteHomology_of_regular (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b)
    (h₀ : Module.length R (H₀ M a b) ≠ ⊤) : HasFiniteHomology M a b := by
  let := subsingleton_H₁_of_regular M a b ha hb
  let := subsingleton_H₂_of_regular M a b ha
  exact ⟨h₀, by simp, by simp⟩

/-- Ordinary quotient length is justified only after higher homology has vanished. -/
theorem eulerMultiplicity_of_regular (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b) (h : HasFiniteHomology M a b) :
    eulerMultiplicity M a b h = ((Module.length R (H₀ M a b)).toNat : ℤ) := by
  let := subsingleton_H₁_of_regular M a b ha hb
  let := subsingleton_H₂_of_regular M a b ha
  simp [eulerMultiplicity]

end Motivic.LocalLength.KoszulPair
