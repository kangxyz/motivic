/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorSingle
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The exterior augmentation after restriction to a field

A resolution over a commutative algebra restricts to a projective resolution
over its arbitrary base field: exactness comes from scalar restriction and
projectivity comes from the vector-space basis theorem. Its literal
augmentation is a homotopy equivalence. Applying the actual tensor bifunctor
and signed totalization to two such augmentations gives a quasi-isomorphism.
No flatness over the algebra, boundedness of the resolutions, Tor symmetry,
or assumed totalization exactness is used.

This file proves the field-level homotopical input. Identifying its total
complex with restriction of the exterior-algebra total complex, and proving
projectivity over that exterior algebra, are separate scalar obligations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace Motivic.TorComparison

variable {k U V : Type u} [Field k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]

/-- Restricting a genuine resolution to the base field again gives a genuine
projective resolution. Vector-space projectivity is proved by existing instances. -/
noncomputable def fieldRestrictedResolution {M : ModuleCat.{u} U}
    (P : ProjectiveResolution M) :
    ProjectiveResolution ((ModuleCat.restrictScalars (algebraMap k U)).obj M) := by
  letI : (ModuleCat.restrictScalars (algebraMap k U)).PreservesProjectiveObjects :=
    ⟨fun _ => inferInstance⟩
  exact (ModuleCat.restrictScalars (algebraMap k U)).mapProjectiveResolution P

/-- The restricted resolution augmentation is itself a homotopy equivalence. -/
noncomputable def fieldRestrictedAugmentationHomotopyEquiv {M : ModuleCat.{u} U}
    (P : ProjectiveResolution M) :
    HomotopyEquiv (fieldRestrictedResolution (k := k) P).complex
      ((ChainComplex.single₀ (ModuleCat k)).obj
        ((ModuleCat.restrictScalars (algebraMap k U)).obj M)) :=
  augmentationHomotopyEquiv (fieldRestrictedResolution (k := k) P)

/-- The comparison over the field still uses the actual restricted augmentation. -/
@[simp]
theorem fieldRestrictedAugmentationHomotopyEquiv_hom {M : ModuleCat.{u} U}
    (P : ProjectiveResolution M) :
    (fieldRestrictedAugmentationHomotopyEquiv (k := k) P).hom =
      (fieldRestrictedResolution (k := k) P).π := rfl

/-- Tensoring two restricted resolution augmentations and taking the signed
nonnegative total complex yields an actual homotopy equivalence. -/
noncomputable def fieldExteriorAugmentationHomotopyEquiv
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    HomotopyEquiv
      (mapBifunctor (fieldRestrictedResolution (k := k) P).complex
        (fieldRestrictedResolution (k := k) Q).complex
        (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ))
      (mapBifunctor
        ((ChainComplex.single₀ (ModuleCat k)).obj
          ((ModuleCat.restrictScalars (algebraMap k U)).obj M))
        ((ChainComplex.single₀ (ModuleCat k)).obj
          ((ModuleCat.restrictScalars (algebraMap k V)).obj N))
        (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)) :=
  exteriorTotalHomotopyEquiv (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)
    (fieldRestrictedAugmentationHomotopyEquiv (k := k) P)
    (fieldRestrictedAugmentationHomotopyEquiv (k := k) Q)

/-- The tensor of the actual restricted augmentations is a quasi-isomorphism
on the actual signed total complexes. -/
theorem fieldExteriorAugmentation_quasiIso
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    QuasiIso (mapBifunctorMap (fieldRestrictedResolution (k := k) P).π
      (fieldRestrictedResolution (k := k) Q).π
      (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)) :=
  (fieldExteriorAugmentationHomotopyEquiv (k := k) P Q).quasiIso_hom

/-- The actual signed exterior total complex of the two restricted resolutions
is a projective resolution over the field of the tensor of the restricted modules. -/
noncomputable def fieldExteriorResolution
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    ProjectiveResolution
      (((curriedTensor (ModuleCat k)).obj
        ((ModuleCat.restrictScalars (algebraMap k U)).obj M)).obj
        ((ModuleCat.restrictScalars (algebraMap k V)).obj N)) where
  complex := mapBifunctor (fieldRestrictedResolution (k := k) P).complex
    (fieldRestrictedResolution (k := k) Q).complex
    (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)
  projective _ := inferInstance
  π := mapBifunctorMap (fieldRestrictedResolution (k := k) P).π
      (fieldRestrictedResolution (k := k) Q).π
      (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ) ≫
    (exteriorSingleIso (curriedTensor (ModuleCat k))
      ((ModuleCat.restrictScalars (algebraMap k U)).obj M)
      ((ModuleCat.restrictScalars (algebraMap k V)).obj N)).hom
  quasiIso := by
    have := fieldExteriorAugmentation_quasiIso (k := k) P Q
    infer_instance

/-- Every positive degree of the constructed exterior complex is exact over k. -/
theorem fieldExteriorResolution_exactAt_succ
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (fieldExteriorResolution (k := k) P Q).complex.ExactAt (n + 1) :=
  (fieldExteriorResolution (k := k) P Q).complex_exactAt_succ n

end Motivic.TorComparison
