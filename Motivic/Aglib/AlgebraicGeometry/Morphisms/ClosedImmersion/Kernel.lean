/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Kernels of closed immersions
-/

@[expose] public noncomputable section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual ideal of a Cartesian intersection of closed immersions is their sum. -/
theorem ker_comp_eq_sup_of_isPullback {W D T P : Scheme.{u}}
    (a : W ⟶ D) (b : W ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
    [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b i j) :
    (a ≫ i).ker = i.ker ⊔ j.ker := by
  let I := i.ker ⊔ j.ker
  apply le_antisymm
  · have hi : i.ker ≤ I.subschemeι.ker := by
      rw [I.ker_subschemeι]
      exact le_sup_left
    have hj : j.ker ≤ I.subschemeι.ker := by
      rw [I.ker_subschemeι]
      exact le_sup_right
    let d := IsClosedImmersion.lift i I.subschemeι hi
    let t := IsClosedImmersion.lift j I.subschemeι hj
    have hd : d ≫ i = I.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have ht : t ≫ j = I.subschemeι := IsClosedImmersion.lift_fac _ _ _
    let w := sq.lift d t (hd.trans ht.symm)
    have hw : w ≫ (a ≫ i) = I.subschemeι := by
      rw [← Category.assoc, IsPullback.lift_fst, hd]
    have hk := Scheme.Hom.le_ker_comp w (a ≫ i)
    rwa [hw, I.ker_subschemeι] at hk
  · exact sup_le (Scheme.Hom.le_ker_comp a i)
      (sq.w.symm ▸ Scheme.Hom.le_ker_comp b j)

/-- Cartesian base change of an actual closed immersion pulls back its kernel ideal. -/
theorem ker_eq_comap_of_isPullback {W D T P : Scheme.{u}}
    (a : W ⟶ D) (b : W ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
    [IsClosedImmersion j] (sq : IsPullback a b i j) :
    a.ker = j.ker.comap i := by
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]


end AlgebraicGeometry.Scheme.Hom
