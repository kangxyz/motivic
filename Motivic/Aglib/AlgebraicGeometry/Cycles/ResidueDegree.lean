/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Residue-field degrees and towers

These are laws for the actual residue-field maps of scheme morphisms.
The degree is mathlib's `Scheme.Hom.residueDegree`, namely the natural-valued
vector-space dimension, with value zero for infinite extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}

/-- The actual residue-field degree satisfies the field-tower formula. -/
theorem residueDegree_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  unfold Scheme.Hom.residueDegree
  rw [Scheme.residueFieldMap_comp]
  let := (f.residueFieldMap x).hom.toAlgebra
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
  have : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  exact (Module.finrank_mul_finrank (Z.residueField (g (f x)))
    (Y.residueField (f x)) (X.residueField x)).symm

/-- An isomorphism has residue-field degree one at every point. -/
@[simp]
theorem residueDegree_of_isIso (f : X ⟶ Y) [IsIso f] (x : X) :
    f.residueDegree x = 1 := by
  have h := residueDegree_comp f (inv f) x
  rw [IsIso.hom_inv_id, Scheme.Hom.residueDegree_id] at h
  exact Nat.eq_one_of_dvd_one ⟨(inv f).residueDegree (f x),
    h.trans (Nat.mul_comm _ _)⟩

/-- A stalk-surjective morphism induces surjective maps on actual residue fields. -/
theorem residueFieldMap_surjective (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  intro a
  obtain ⟨s, hs⟩ := X.residue_surjective x a
  obtain ⟨t, ht⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  change (Y.residue (f x) ≫ f.residueFieldMap x) t = a
  rw [Scheme.residue_residueFieldMap]
  simpa only [CommRingCat.comp_apply, ht] using hs

/-- Closed immersions, and more generally stalk-surjective maps, have residue degree one. -/
theorem residueDegree_of_surjectiveOnStalks (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    f.residueDegree x = 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    ⟨(f.residueFieldMap x).hom.injective, residueFieldMap_surjective f x⟩

end AlgebraicGeometry.Scheme.Hom
