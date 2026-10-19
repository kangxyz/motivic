module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Invariants

/-! # Removing the actual identity-point rational function

The signed-unit kernel is the product of M* with the cyclic subgroup generated
by X - 1, and those two factors meet trivially.
-/

@[expose] public noncomputable section

namespace Polynomial.BoundaryOneRationalFunctions

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The actual normalized rational function whose divisor is the identity point. -/
def identityPointFraction : admissibleGroup R :=
  admissibleFraction (linearDenominator (-1 : Rˣ)) 1

@[simp] theorem fractionDegree_identityPoint :
    fractionDegree (identityPointFraction (R := R)) = 1 := by
  simp [identityPointFraction]

@[simp] theorem signedValueHom_identityPoint :
    signedValueHom (identityPointFraction (R := R)) = 1 := by
  change (-1 : Rˣ) ^ fractionDegree identityPointFraction *
    zeroValueHom identityPointFraction = 1
  have h : denominatorConstant (1 : denominators R) = 1 := by
    apply Units.ext
    simp
  simp [identityPointFraction, h]

@[simp] theorem degreeHom_identityPoint :
    degreeHom (identityPointFraction (R := R)) = Multiplicative.ofAdd (1 : ℤ) :=
  congrArg Multiplicative.ofAdd fractionDegree_identityPoint

/-- A signed-unit-trivial actual function becomes boundary-one after removing
its actual degree multiple of X - 1. -/
theorem identityPoint_normalize_mem (f : admissibleGroup R) (hf : signedValueHom f = 1) :
    (f / identityPointFraction ^ fractionDegree f).val ∈ group R := by
  apply (boundaryInvariant_eq_one_iff _).mp
  apply Prod.ext
  · change degreeHom (f / identityPointFraction ^ fractionDegree f) = 1
    rw [_root_.map_div, map_zpow, degreeHom_identityPoint]
    apply Multiplicative.toAdd.injective
    change fractionDegree f - fractionDegree f • (1 : ℤ) = 0
    simp
  · change signedValueHom (f / identityPointFraction ^ fractionDegree f) = 1
    rw [_root_.map_div, map_zpow, hf, signedValueHom_identityPoint]
    simp

/-- The signed-unit kernel decomposes into the genuine M* subgroup and identity point. -/
theorem signedValue_kernel_decomposition (f : admissibleGroup R) (hf : signedValueHom f = 1) :
    ∃ m : group R,
      f = boundaryInclusion m * identityPointFraction ^ fractionDegree f := by
  let m : group R := ⟨(f / identityPointFraction ^ fractionDegree f).val,
    identityPoint_normalize_mem f hf⟩
  refine ⟨m, ?_⟩
  have h : boundaryInclusion m = f / identityPointFraction ^ fractionDegree f := rfl
  rw [h, div_mul_cancel]

/-- The boundary-one subgroup and the actual identity-point powers intersect trivially. -/
theorem boundary_identityPoint_intersection (m : group R) (d : ℤ)
    (h : boundaryInclusion m = identityPointFraction ^ d) : m = 1 ∧ d = 0 := by
  have hb := (boundary_iff_degree_zeroValue (boundaryInclusion m)).mp m.property
  have hd := congrArg degreeHom h
  rw [map_zpow, degreeHom_identityPoint] at hd
  have ht := congrArg Multiplicative.toAdd hd
  change fractionDegree (boundaryInclusion m) = d • (1 : ℤ) at ht
  have hd0 : d = 0 := by simpa [hb.1] using ht.symm
  refine ⟨boundaryInclusion_injective ?_, hd0⟩
  simpa [hd0] using h

end Polynomial.BoundaryOneRationalFunctions
