/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.MvPolynomial.Diagonal
public import Motivic.Algebra.Homology.KoszulPairTor

/-!
# The genuine Koszul resolution of the polynomial plane diagonal

The two coordinate differences are proved regular on the polynomial ambient
ring over an arbitrary commutative base. They therefore instantiate the actual
Koszul projective resolution and categorical Tor computation. The coefficient
module in the Tor computation is arbitrary: no regularity is assumed on it.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory RingTheory.Sequence
open scoped Pointwise
open Motivic.LocalLength.KoszulPair

namespace Motivic.PolynomialDiagonal

variable (R : Type u) [CommRing R]

/-- The plane diagonal has exactly the two stated coordinate-difference generators. -/
theorem ideal_fin_two : ideal R (Fin 2) =
    Ideal.span ({difference R (Fin 2) 0, difference R (Fin 2) 1} : Set (Ambient R (Fin 2))) := by
  unfold ideal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The first plane-diagonal difference is regular on the ambient ring. -/
theorem isSMulRegular_difference_zero :
    IsSMulRegular (Ambient R (Fin 2)) (difference R (Fin 2) 0) := by
  have h := isWeaklyRegular_differences R (Fin 2) [0, 1] (by decide)
  simp only [List.map_cons, List.map_nil, isWeaklyRegular_cons_iff] at h
  exact h.1

/-- The second plane-diagonal difference is regular modulo the first. -/
theorem isSMulRegular_difference_one :
    IsSMulRegular (PrincipalQuotient (Ambient R (Fin 2)) (difference R (Fin 2) 0))
      (difference R (Fin 2) 1) := by
  have h := isWeaklyRegular_differences R (Fin 2) [0, 1] (by decide)
  simp only [List.map_cons, List.map_nil, isWeaklyRegular_cons_iff] at h
  have heq : (difference R (Fin 2) 0) • (⊤ : Submodule (Ambient R (Fin 2))
      (Ambient R (Fin 2))) =
      LinearMap.range (LinearMap.lsmul (Ambient R (Fin 2)) (Ambient R (Fin 2))
        (difference R (Fin 2) 0)) := by
    rw [Submodule.pointwise_smul_def, Submodule.map_top]
    rfl
  exact ((Submodule.quotEquivOfEq _ _ heq).isSMulRegular_congr _).mp h.2.1

/-- The proved length-two projective resolution of the genuine plane-diagonal quotient. -/
def planeProjectiveResolution :
    ProjectiveResolution (ModuleCat.of (Ambient R (Fin 2))
      (Ambient R (Fin 2) ⧸ ideal R (Fin 2))) := by
  rw [ideal_fin_two]
  exact idealProjectiveResolution _ _ (isSMulRegular_difference_zero R)
    (isSMulRegular_difference_one R)

variable (M : Type u) [AddCommGroup M] [Module (Ambient R (Fin 2)) M]

/-- Actual Tor against the plane diagonal, retaining arbitrary coefficient-module homology. -/
def planeTorIsoHomology (n : ℕ) :
    ((Tor (ModuleCat (Ambient R (Fin 2))) n).obj (ModuleCat.of _ M)).obj
      (ModuleCat.of _ (Ambient R (Fin 2) ⧸ ideal R (Fin 2))) ≅
        (chainComplex M (difference R (Fin 2) 0) (difference R (Fin 2) 1)).homology n := by
  rw [ideal_fin_two]
  exact torIdealIsoHomology M _ _ (isSMulRegular_difference_zero R)
    (isSMulRegular_difference_one R) n

end Motivic.PolynomialDiagonal
