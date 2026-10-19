/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# The Bockstein on actual cohomology objects

The coefficient connecting map induces a map from the homology object in
degree `i` to the integral homology object in degree `i+1`, using mathlib's
canonical shift isomorphism. The representative formula is proved: a cocycle
with signed coordinates `(a,b)` maps to the homology class of `b` with positive
sign. Neither cohomology groups nor the Bockstein are supplied as assumptions.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive CochainComplex HomologicalComplex

universe u v

namespace CochainComplex.finiteCoefficients

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryWithHomology C] (K : CochainComplex C ℤ) (n : ℕ)

/-- The coefficient Bockstein on actual cohomology objects, including the shift identification. -/
noncomputable def bocksteinHomology (i : ℤ) :
    (finiteCoefficients K n).homology i ⟶ K.homology (i + 1) :=
  homologyMap (bockstein K n) i ≫
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
      1 i (i + 1) (add_comm 1 i)).hom.app K

omit [CategoryWithHomology C] in
/-- The positive coordinate of a coefficient cocycle is an integral cocycle. -/
theorem cycle_b {A : C} (i : ℤ) (x : A ⟶ (finiteCoefficients K n).X i)
    (hx : x ≫ (finiteCoefficients K n).d i (i + 1) = 0) :
    (x ≫ b K n i) ≫ K.d (i + 1) (i + 1 + 1) = 0 := by
  have h := congrArg (fun f => f ≫ b K n (i + 1)) hx
  simpa [d_b, assoc] using h

/-- A cohomology class represented by `(a,b)` has Bockstein represented by `b`.
This equality uses the canonical homology shift isomorphism and fixes its sign. -/
@[reassoc]
theorem bocksteinHomology_liftCycles {A : C} (i : ℤ)
    (x : A ⟶ (finiteCoefficients K n).X i)
    (hx : x ≫ (finiteCoefficients K n).d i (i + 1) = 0) :
    (finiteCoefficients K n).liftCycles x (i + 1)
        ((ComplexShape.up ℤ).next_eq' rfl) hx ≫
      (finiteCoefficients K n).homologyπ i ≫ bocksteinHomology K n i =
    K.liftCycles (x ≫ b K n i) (i + 1 + 1)
        ((ComplexShape.up ℤ).next_eq' rfl) (cycle_b K n i x hx) ≫
      K.homologyπ (i + 1) := by
  dsimp only [bocksteinHomology]
  rw [homologyπ_naturality_assoc, ← assoc, liftCycles_comp_cyclesMap]
  rw [liftCycles_shift_homologyπ_assoc K _ (i + 1) ((ComplexShape.up ℤ).next_eq' rfl)
    _ (i + 1) (add_comm 1 i) (i + 1 + 1) ((ComplexShape.up ℤ).next_eq' rfl)]
  simp only [bockstein_f, shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv,
    Iso.refl_hom, comp_id, Iso.inv_hom_id_app]
  change _ ≫ _ ≫ 𝟙 (K.homology (i + 1)) = _
  simp only [comp_id]
  apply congrArg (fun f : A ⟶ K.cycles (i + 1) => f ≫ K.homologyπ (i + 1))
  apply (cancel_mono (K.iCycles (i + 1))).1
  simp only [liftCycles_i]
  exact Category.comp_id _

end CochainComplex.finiteCoefficients
