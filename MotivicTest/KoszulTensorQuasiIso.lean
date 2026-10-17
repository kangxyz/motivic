/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulTensorQuasiIso
public import Motivic.Algebra.Homology.KoszulFiniteResolution

/-! Consumer checks for actual finite Koszul tensor invariance and resolution augmentation. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Motivic.MotivicTest.KoszulTensorQuasiIso

variable {R : Type u} [CommRing R]

/-- The coefficient complexes need not be bounded, projective, flat, or regular. -/
theorem arbitraryComplexes (s : List R)
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (Koszul.chainComplex s ◁ f) :=
  Koszul.tensor_quasiIso f s

/-- In particular two zero scalars, a nonregular list in every nonzero ring, are allowed. -/
theorem zeroScalars {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (Koszul.chainComplex ([0, 0] : List R) ◁ f) :=
  Koszul.tensor_quasiIso f ([0, 0] : List R)

/-- The double-complex augmentation needed for derived tensor comparisons is genuine. -/
theorem resolutionAugmentation (s : List R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) : QuasiIso (Koszul.chainComplex s ◁ P.π) :=
  Koszul.tensor_resolution_quasiIso s P

/-- The actual constructed Koszul resolution can be used in the resolved argument. -/
theorem finiteResolutionAugmentation (s t : List R)
    (ht : RingTheory.Sequence.IsWeaklyRegular R t) :
    QuasiIso (Koszul.chainComplex s ◁ Koszul.idealAugmentation t) := by
  have : QuasiIso (Koszul.idealAugmentation t) :=
    Koszul.idealAugmentation_quasiIso_of_weaklyRegular t ht
  exact Koszul.tensor_quasiIso (Koszul.idealAugmentation t) s

/-- Every homological degree of the double resolution has the actual coefficient comparison. -/
noncomputable def resolutionHomology (s : List R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (n : ℕ) :
    (HomologicalComplex.tensorObj (Koszul.chainComplex s) P.complex).homology n ≅
      (HomologicalComplex.tensorObj (Koszul.chainComplex s)
        ((ChainComplex.single₀ (ModuleCat R)).obj M)).homology n :=
  Koszul.tensorResolutionHomologyIso s P n

end Motivic.MotivicTest.KoszulTensorQuasiIso
