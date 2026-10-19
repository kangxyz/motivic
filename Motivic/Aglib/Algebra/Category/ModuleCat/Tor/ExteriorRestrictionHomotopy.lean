/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.ExteriorFieldAugmentation

/-!
# The literal scalar-restriction image of a resolution augmentation

The target of the literal image of an augmentation is the restriction of the
original single complex. It is canonically isomorphic, but not definitionally
identical, to the single complex of the restricted module. This file retains
that target and fixes the forward homotopy-equivalence map to be the literal
image of the original augmentation, for later naturality of total complexes.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe u

namespace ModuleCat.TorComparison

variable {k U : Type u} [Field k] [CommRing U] [Algebra k U]

/-- The literal image under field restriction of a resolution augmentation is a
homotopy equivalence, with its original mapped-single target. -/
noncomputable def fieldRestrictionAugmentationHomotopyEquiv
    {M : ModuleCat.{u} U} (P : ProjectiveResolution M) :
    HomotopyEquiv
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex)
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj ((ChainComplex.single₀ (ModuleCat U)).obj M)) := by
  let e := (fieldRestrictedAugmentationHomotopyEquiv (k := k) P).trans
    (HomotopyEquiv.ofIso
      ((singleMapHomologicalComplex (ModuleCat.restrictScalars (algebraMap k U))
        (ComplexShape.down ℕ) 0).app M).symm)
  refine e.copy (g := ((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map P.π) (Homotopy.ofEq ?_)
  change (fieldRestrictedResolution (k := k) P).π ≫ _ = _
  dsimp only [fieldRestrictedResolution, Functor.mapProjectiveResolution]
  simp [HomotopyEquiv.ofIso]

/-- The forward map is definitionally the image of the actual augmentation. -/
@[simp]
theorem fieldRestrictionAugmentationHomotopyEquiv_hom
    {M : ModuleCat.{u} U} (P : ProjectiveResolution M) :
    (fieldRestrictionAugmentationHomotopyEquiv (k := k) P).hom =
      ((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map P.π := rfl

end ModuleCat.TorComparison
