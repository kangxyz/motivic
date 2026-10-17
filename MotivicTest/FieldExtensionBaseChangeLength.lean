/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.FieldExtensionBaseChangeLength
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorGeneric
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Original pair residue maps and nonreduced tensor degree-length consumers

The original incidence morphism supplies the finite field extension, and the
right-hand degree is its literal finite-pushforward residue degree. The generic
whole-open consumer uses the original pair point already constructed by exterior
projection. These are algebraic specializations: identification of the tensor
local rings with actual exterior support stalk quotients is still separate.

The dual-number consumer retains a genuine nonzero square-zero element in the
base ring. Field base change is unrestricted, including inseparable extensions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open scoped TensorProduct

universe u v

namespace MotivicTest.FieldExtensionBaseChangeLength

open LocalLength

section Algebra

variable (K L E : Type u) [Field K] [Field L] [Field E]
  [Algebra K L] [Module.Finite K L] [Algebra K E]

omit L E [Field L] [Field E] [Algebra K L] [Module.Finite K L] [Algebra K E] in
/-- The ordinary square-zero extension of a field is local. -/
local instance squareZeroBase_local : IsLocalRing (TrivSqZeroExt K K) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    have hf : a.fst + b.fst = 1 := congrArg TrivSqZeroExt.fst h
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst] using
      (IsLocalRing.isUnit_or_isUnit_of_add_one hf)

/-- A field base gives the all-branch degree formula without any separability assumption. -/
theorem arbitraryFieldBase :
    fieldExtensionBaseChangeLengthSum K L E = (Module.finrank K L : ℕ∞) := by
  rw [fieldExtensionBaseChangeLengthSum_eq, Module.length_eq_one, mul_one]

omit E [Field E] [Algebra K E] in
/-- Dual numbers are a genuine Artinian local base for the same all-branch formula. -/
theorem dualNumberBase :
    fieldExtensionBaseChangeLengthSum K L (TrivSqZeroExt K K) =
      (Module.finrank K L : ℕ∞) * Module.length (TrivSqZeroExt K K) (TrivSqZeroExt K K) := by
  have : Module.Finite K (TrivSqZeroExt K K) := inferInstanceAs (Module.Finite K (K × K))
  have : IsScalarTower K (TrivSqZeroExt K K) (TrivSqZeroExt K K) := ⟨by
    intro a b c
    ext <;> simp [mul_add, mul_assoc]⟩
  have : IsArtinianRing (TrivSqZeroExt K K) := IsArtinianRing.of_finite K (TrivSqZeroExt K K)
  exact fieldExtensionBaseChangeLengthSum_eq K L (TrivSqZeroExt K K)

omit L E [Field L] [Field E] [Algebra K L] [Module.Finite K L] [Algebra K E] in
/-- The Artinian base in the preceding consumer has a nonzero nilpotent. -/
theorem dualNumberBaseHasNilpotent :
    (TrivSqZeroExt.inr 1 : TrivSqZeroExt K K) ≠ 0 ∧
      (TrivSqZeroExt.inr 1 : TrivSqZeroExt K K) * TrivSqZeroExt.inr 1 = 0 := by
  refine ⟨?_, by simp⟩
  intro h
  have := congrArg TrivSqZeroExt.snd h
  simp at this

end Algebra

section OriginalPair

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (z : genericPoints (F.incidence G))

/-- The literal original pair-incidence residue homomorphism supplies the algebra. -/
local instance pairResidueAlgebra :
    Algebra ((pullback X.hom Z.hom).residueField (F.incidenceMap G z.1))
      ((F.incidence G).residueField z.1) :=
  ((F.incidenceMap G).residueFieldMap z.1).hom.toAlgebra

/-- Finiteness comes from the actual finite pair-incidence morphism. -/
local instance pairResidueFinite :
    Module.Finite ((pullback X.hom Z.hom).residueField (F.incidenceMap G z.1))
      ((F.incidence G).residueField z.1) :=
  residueFieldMap_finite (F.incidenceMap G) z.1

variable (R : Type v) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  [Algebra ((pullback X.hom Z.hom).residueField (F.incidenceMap G z.1)) R]

/-- The extension degree is literally the original pair-incidence pushforward degree. -/
theorem actualPairResidueDegreeBalance :
    fieldExtensionBaseChangeLengthSum
        ((pullback X.hom Z.hom).residueField (F.incidenceMap G z.1))
        ((F.incidence G).residueField z.1) R =
      ((F.incidenceMap G).residueDegree z.1 : ℕ∞) * Module.length R R :=
  fieldExtensionBaseChangeLengthSum_eq _ _ R

omit [IsLocalRing R] [IsArtinianRing R] in
/-- The tensor square uses the original incidence residue homomorphism itself. -/
theorem actualPairResidueScalarSquare :
    (Algebra.TensorProduct.includeLeftRingHom.comp
        (algebraMap ((pullback X.hom Z.hom).residueField (F.incidenceMap G z.1)) R) :
      ((pullback X.hom Z.hom).residueField (F.incidenceMap G z.1)) →+*
        R ⊗[((pullback X.hom Z.hom).residueField (F.incidenceMap G z.1))]
          ((F.incidence G).residueField z.1)) =
      Algebra.TensorProduct.includeRight.toRingHom.comp
        ((F.incidenceMap G).residueFieldMap z.1).hom :=
  fieldExtensionBaseChange_square _ _ R

end OriginalPair

section WholeOpen

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (w : genericPoints (F.firstStageWholeOpen G H V))
  (R : Type v) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  [Algebra ((pullback X.hom Z.hom).residueField
    (F.incidenceMap G (F.firstStageWholeGenericPair G H V w).1)) R]

/-- The original whole-open pair point supplies its own actual field map and degree.
The Artinian exterior support-ring attachment has not been assumed or asserted. -/
theorem actualWholePairResidueDegreeBalance :
    letI := ((F.incidenceMap G).residueFieldMap
      (F.firstStageWholeGenericPair G H V w).1).hom.toAlgebra
    letI : Module.Finite
        ((pullback X.hom Z.hom).residueField
          (F.incidenceMap G (F.firstStageWholeGenericPair G H V w).1))
        ((F.incidence G).residueField (F.firstStageWholeGenericPair G H V w).1) :=
      residueFieldMap_finite (F.incidenceMap G) (F.firstStageWholeGenericPair G H V w).1
    fieldExtensionBaseChangeLengthSum
        ((pullback X.hom Z.hom).residueField
          (F.incidenceMap G (F.firstStageWholeGenericPair G H V w).1))
        ((F.incidence G).residueField (F.firstStageWholeGenericPair G H V w).1) R =
      ((F.incidenceMap G).residueDegree (F.firstStageWholeGenericPair G H V w).1 : ℕ∞) *
        Module.length R R :=
  actualPairResidueDegreeBalance F G (F.firstStageWholeGenericPair G H V w) R

end WholeOpen

end MotivicTest.FieldExtensionBaseChangeLength
