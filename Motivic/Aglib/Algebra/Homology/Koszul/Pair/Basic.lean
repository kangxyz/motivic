/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.LocalLength.KoszulPair
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The categorical two-element Koszul chain complex

The literal module maps `d₂(z) = (-b • z, a • z)` and
`d₁(x,y) = a • x + b • y` define an actual nonnegative chain complex,
with zero terms above degree two. Its categorical homology is identified
with the explicit kernel and quotient modules from the local-length API.
No exactness or comparison is supplied as a hypothesis of a data record.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Module.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

/-- The terms of the two-element Koszul chain complex. -/
noncomputable def chainX : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R M
  | 1 => ModuleCat.of R (M × M)
  | 2 => ModuleCat.of R M
  | _ + 3 => 0

/-- The successive differentials of the two-element Koszul chain complex. -/
noncomputable def chainD : (n : ℕ) → chainX (R := R) M (n + 1) ⟶ chainX (R := R) M n
  | 0 => ModuleCat.ofHom (d₁ M a b)
  | 1 => ModuleCat.ofHom (d₂ M a b)
  | _ + 2 => 0

/-- The actual categorical Koszul complex, supported in degrees zero through two. -/
noncomputable def chainComplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (chainX (R := R) M) (chainD M a b) (by
    intro n
    cases n with
    | zero => exact ModuleCat.hom_ext (LinearMap.ext (d₁_d₂ M a b))
    | succ n => cases n <;> exact zero_comp)

@[simp]
theorem chainComplex_X_zero : (chainComplex M a b).X 0 = ModuleCat.of R M := rfl

@[simp]
theorem chainComplex_X_one : (chainComplex M a b).X 1 = ModuleCat.of R (M × M) := rfl

@[simp]
theorem chainComplex_X_two : (chainComplex M a b).X 2 = ModuleCat.of R M := rfl

@[simp]
theorem chainComplex_X_add_three (n : ℕ) : (chainComplex M a b).X (n + 3) = 0 := rfl

@[simp]
theorem chainComplex_d_one_zero :
    (chainComplex M a b).d 1 0 = ModuleCat.ofHom (d₁ M a b) := by
  exact ChainComplex.of_d (chainX (R := R) M) (chainD M a b) 0

@[simp]
theorem chainComplex_d_two_one :
    (chainComplex M a b).d 2 1 = ModuleCat.ofHom (d₂ M a b) := by
  exact ChainComplex.of_d (chainX (R := R) M) (chainD M a b) 1

@[simp]
theorem chainComplex_d_add_three (n : ℕ) :
    (chainComplex M a b).d (n + 3) (n + 2) = 0 := by
  exact ChainComplex.of_d (chainX (R := R) M) (chainD M a b) (n + 2)

/-- Categorical degree-zero homology is the literal quotient by `d₁`. -/
noncomputable def homologyZeroIso :
    (chainComplex M a b).homology 0 ≅ ModuleCat.of R (H₀ M a b) :=
  (chainComplex M a b).isoHomologyι₀ ≪≫
    (chainComplex M a b).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    ((chainComplex M a b).sc' 1 0 0).moduleCatOpcyclesIso

/-- Categorical degree-one homology is the literal cycles modulo boundaries. -/
noncomputable def homologyOneIso :
    (chainComplex M a b).homology 1 ≅ ModuleCat.of R (H₁ M a b) := by
  refine (chainComplex M a b).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫ ?_
  exact
    ((chainComplex M a b).sc' 2 1 0).moduleCatHomologyIso

/-- Categorical degree-two homology is the literal kernel of `d₂`. -/
noncomputable def homologyTwoIso :
    (chainComplex M a b).homology 2 ≅ ModuleCat.of R (H₂ M a b) := by
  refine ((chainComplex M a b).isoHomologyπ 3 2 (by simp)
    (chainComplex_d_add_three M a b 0)).symm ≪≫
    (chainComplex M a b).cyclesIsoSc' 3 2 1 (by simp) (by simp) ≪≫ ?_
  exact
    ((chainComplex M a b).sc' 3 2 1).moduleCatCyclesIso

/-- There are no homology terms above the two Koszul equations. -/
theorem exactAt_add_three (n : ℕ) : (chainComplex M a b).ExactAt (n + 3) :=
  HomologicalComplex.ExactAt.of_isZero (by
    change IsZero (0 : ModuleCat.{v} R)
    exact isZero_zero _)

/-- A regular pair makes the actual categorical complex exact in degree one. -/
theorem exactAt_one_of_regular (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b) :
    (chainComplex M a b).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have := subsingleton_H₁_of_regular M a b ha hb
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (H₁ M a b))).of_iso
    (homologyOneIso M a b)

/-- A regular first scalar makes the actual categorical complex exact in degree two. -/
theorem exactAt_two_of_regular (ha : IsSMulRegular M a) :
    (chainComplex M a b).ExactAt 2 := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have := subsingleton_H₂_of_regular M a b ha
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (H₂ M a b))).of_iso
    (homologyTwoIso M a b)

end Module.KoszulPair
