/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.OpenRestrictionStalk
public import Motivic.AlgebraicGeometry.Cycles.FiniteAffineChart
public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists

/-!
# Actual whole-preimage and quotient-module stalk restriction consumers

The comparisons apply to arbitrary original sheaf complexes on a finite-map
source and to genuine quotient tilde modules. The actual intermediate-image
map consumes the scalar-compatible comparison at every source chart point.
No first-stage coefficient sheaf is postulated or constructed here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.OpenRestrictionStalk

open Motivic.ModuleStalk Motivic.FiniteAffineChart

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U)
  (q : Spec Γ(X, f ⁻¹ᵁ U))

/-- An arbitrary original sheaf complex has the actual stalk complex after
restriction to the entire affine inverse image, with the canonical ring action. -/
def wholeFinitePreimageComplex (K : ChainComplex X.Modules ℕ) :
    (((Scheme.Modules.restrictFunctor (sourceChart f hU) ⋙
      functor q).mapHomologicalComplex _).obj K) ≅
    (((functor (sourceChart f hU q) ⋙ ModuleCat.restrictScalars
      (inv ((sourceChart f hU).stalkMap q)).hom).mapHomologicalComplex _).obj K) :=
  (openRestrictionComplexIso (sourceChart f hU) q _).app K

/-- The original differentials are preserved at every degree after whole
finite-preimage restriction, without homology or termwise finiteness premises. -/
theorem wholeFinitePreimageDifferential (K : ChainComplex X.Modules ℕ) (n m : ℕ) :
    (((Scheme.Modules.restrictFunctor (sourceChart f hU) ⋙
      functor q).mapHomologicalComplex _).obj K).d n m ≫
        (wholeFinitePreimageComplex f hU q K).hom.f m =
      (wholeFinitePreimageComplex f hU q K).hom.f n ≫
        (((functor (sourceChart f hU q) ⋙ ModuleCat.restrictScalars
          (inv ((sourceChart f hU).stalkMap q)).hom).mapHomologicalComplex _).obj K).d n m :=
  openRestrictionComplexIso_hom_comm (sourceChart f hU) q _ K n m

/-- A genuine quotient tilde module, including arbitrary nonradical ideals,
retains its actual O-stalk action under restriction to an arbitrary open. -/
def quotientTildeRestriction (A : CommRingCat.{u}) (I : Ideal A)
    (V : (Spec A).Opens) (x : V) :
    ((Scheme.Modules.restrictFunctor V.ι ⋙ functor x).obj (tilde (ModuleCat.of A (A ⧸ I)))) ≅
      ((functor (V.ι x) ⋙ ModuleCat.restrictScalars (inv (V.ι.stalkMap x)).hom).obj
        (tilde (ModuleCat.of A (A ⧸ I)))) :=
  (openRestrictionIso V.ι x).app _

variable {S X₀ Y₀ Z₀ W₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ S} {g₀ : Y₀ ⟶ S} {h₀ : Z₀ ⟶ S} {i₀ : W₀ ⟶ S}
  (F : FiniteCorrespondenceGenerator f₀ g₀) (G : FiniteCorrespondenceGenerator g₀ h₀)
  (H : FiniteCorrespondenceGenerator h₀ i₀) [IsSeparated h₀]
  {V : (F.leftIntermediateImageProduct G H).Opens} (hV : IsAffineOpen V)
  (v : Spec Γ(F.leftIntermediateSupportProduct G H,
    (F.leftIntermediateImageMap G H) ⁻¹ᵁ V))

/-- Every actual sheaf module on the genuine first-stage support has its
canonical module-stalk comparison at every point of the whole finite chart. -/
def actualIntermediateSupportStalk
    (M : (F.leftIntermediateSupportProduct G H).Modules) :
    ((Scheme.Modules.restrictFunctor
        (sourceChart (F.leftIntermediateImageMap G H) hV) ⋙ functor v).obj M) ≅
      ((functor (sourceChart (F.leftIntermediateImageMap G H) hV v) ⋙
        ModuleCat.restrictScalars
          (inv ((sourceChart (F.leftIntermediateImageMap G H) hV).stalkMap v)).hom).obj M) :=
  (openRestrictionIso (sourceChart (F.leftIntermediateImageMap G H) hV) v).app M

end Motivic.MotivicTest.OpenRestrictionStalk
