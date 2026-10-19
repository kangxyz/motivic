/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.Algebra.Homology.LengthEuler.Chain
import Motivic.Aglib.Algebra.Homology.LengthEuler.Single

/-!
# Consumers of genuine finite-length homology Euler characteristics

These examples use actual categorical complexes, including a single complex
on a residue module over a general commutative ring. The residue module is
not assumed free, and the coefficient ring is not assumed to be a field.
-/

open CategoryTheory HomologicalComplex _root_.HomologicalComplex.ModuleLengthEuler

universe u v

namespace MotivicTest.LengthEuler

variable {R : Type u} [CommRing R]

example {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) [QuasiIso f]
    (hK : FiniteHomology K) :
    chainEuler K hK = chainEuler L (hK.of_quasiIso f) :=
  homologyEuler_eq_of_quasiIso f _ _ _

example (S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ)) (hS : S.ShortExact)
    (hA : FiniteHomology S.X₁) (hB : FiniteHomology S.X₂) (hC : FiniteHomology S.X₃) :
    cochainEuler S.X₂ hB = cochainEuler S.X₁ hA + cochainEuler S.X₃ hC :=
  cochainEuler_add_of_shortExact S hS hA hB hC

example (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (hA : FiniteHomology S.X₁) (hB : FiniteHomology S.X₂) (hC : FiniteHomology S.X₃) :
    chainEuler S.X₂ hB = chainEuler S.X₁ hA + chainEuler S.X₃ hC :=
  chainEuler_add_of_shortExact S hS hA hB hC

/-- A finite-length module in degree one contributes its negative length. -/
example (M : ModuleCat.{v} R) (hM : Module.length R M ≠ ⊤) :
    cochainEuler ((single (ModuleCat R) (ComplexShape.up ℤ) 1).obj M)
      (finiteHomology_single _ _ M hM) = -integerLength M hM := by
  simpa [Int.negOnePow_one] using homologyEuler_single (ComplexShape.up ℤ) 1 M
    (fun i => (i.negOnePow : ℤ)) hM

/-- The residue module contributes one over the original ring, without a freeness premise. -/
example (I : Ideal R) (hI : I.IsMaximal) :
    ∃ h : FiniteHomology
        ((single (ModuleCat R) (ComplexShape.down ℕ) 0).obj (ModuleCat.of R (R ⧸ I))),
      chainEuler ((single (ModuleCat R) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of R (R ⧸ I))) h = 1 := by
  have hlen : Module.length R (R ⧸ I) = 1 := by
    apply Module.length_eq_one_iff.mpr
    exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hI)
  have hfin : Module.length R (R ⧸ I) ≠ ⊤ := by simp [hlen]
  refine ⟨finiteHomology_single _ _ _ hfin, ?_⟩
  simpa [integerLength, hlen] using homologyEuler_single (ComplexShape.down ℕ) 0
    (ModuleCat.of R (R ⧸ I)) (fun i => (-1 : ℤ) ^ i) hfin

end MotivicTest.LengthEuler
