/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorFieldAugmentation
public import Motivic.Algebra.Homology.TorComparison.ExteriorMapQuasiIso
public import Motivic.Algebra.Homology.TorComparison.ExteriorRestrictionHomotopy

/-! Consumer checks for genuine exterior totalization homotopies over an arbitrary field. -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace Motivic.MotivicTest.TorComparisonExteriorHomotopy

variable {k U V : Type u} [Field k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]

/-- Algebra-projective resolutions are honest field-projective resolutions on restriction. -/
noncomputable def restrictResolution {M : ModuleCat.{u} U}
    (P : ProjectiveResolution M) :
    ProjectiveResolution ((ModuleCat.restrictScalars (algebraMap k U)).obj M) :=
  TorComparison.fieldRestrictedResolution P

/-- No projectivity hypothesis on the original resolved module is needed. -/
noncomputable def splitRestrictedAugmentation {M : ModuleCat.{u} U}
    (P : ProjectiveResolution M) :
    HomotopyEquiv (TorComparison.fieldRestrictedResolution (k := k) P).complex
      ((ChainComplex.single₀ (ModuleCat k)).obj
        ((ModuleCat.restrictScalars (algebraMap k U)).obj M)) :=
  TorComparison.fieldRestrictedAugmentationHomotopyEquiv P

/-- The resulting quasi-isomorphism is the actual map of both augmentations. -/
theorem tensorRestrictedAugmentations {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    QuasiIso (mapBifunctorMap (TorComparison.fieldRestrictedResolution (k := k) P).π
      (TorComparison.fieldRestrictedResolution (k := k) Q).π
      (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)) :=
  TorComparison.fieldExteriorAugmentation_quasiIso P Q

/-- The signed total is packaged as an honest projective resolution over the field. -/
noncomputable def tensorResolution {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    ProjectiveResolution
      (((curriedTensor (ModuleCat k)).obj
        ((ModuleCat.restrictScalars (algebraMap k U)).obj M)).obj
        ((ModuleCat.restrictScalars (algebraMap k V)).obj N)) :=
  TorComparison.fieldExteriorResolution P Q

/-- Positive total exactness follows for arbitrary algebra resolutions over any field. -/
theorem positiveTotalExact {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor (TorComparison.fieldRestrictedResolution (k := k) P).complex
      (TorComparison.fieldRestrictedResolution (k := k) Q).complex
      (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)).ExactAt (n + 1) :=
  TorComparison.fieldExteriorResolution_exactAt_succ P Q n

/-- Scalar restriction really preserves the diagonal coproducts in the total comparison. -/
noncomputable def restrictSignedTotal {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (K : HomologicalComplex₂ (ModuleCat.{u} S) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    (TorComparison.exteriorMapBicomplex (ModuleCat.restrictScalars f) K).total
        (ComplexShape.down ℕ) ≅
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (K.total (ComplexShape.down ℕ)) :=
  TorComparison.exteriorMapTotalIso (ModuleCat.restrictScalars f) K (ComplexShape.down ℕ)

/-- The homotopy comparison retains the literal scalar image of the original augmentation. -/
noncomputable def literalRestrictedAugmentation {M : ModuleCat.{u} U}
    (P : ProjectiveResolution M) :
    HomotopyEquiv
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex)
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj ((ChainComplex.single₀ (ModuleCat U)).obj M)) :=
  TorComparison.fieldRestrictionAugmentationHomotopyEquiv P

end Motivic.MotivicTest.TorComparisonExteriorHomotopy
