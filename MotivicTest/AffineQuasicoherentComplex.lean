/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.AffineQuasicoherentComplex
public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists
public import Motivic.Algebra.Homology.KoszulCoefficientComplex

/-!
# Actual quasi-coherent whole-chart complex consumers

A genuine quotient-coefficient Koszul complex supplies a concrete QC sheaf
complex without regularity. Given actual QC complexes on the original
intermediate support, whole finite charts preserve their exact stalk modules
and original differentials. No first-stage coefficient existence is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.AffineQuasicoherentComplex

open Motivic.AffineQuasicoherent Motivic.FiniteAffineChart Motivic.ModuleStalk

/-- A genuine arbitrary-ideal coefficient Koszul complex is recovered from
its actual sheaf global sections, without regularity or reducedness. -/
def quotientKoszulCoordinates (A : CommRingCat.{u}) (I : Ideal A) (s : List A) :
    let L := ((tilde.functor A).mapHomologicalComplex _).obj
      (Koszul.coefficientComplex (ModuleCat.of A (A ⧸ I)) s)
    ((tilde.functor A).mapHomologicalComplex _).obj
      (coordinateComplex A _ L) ≅ L := by
  intro L
  have (n : ℕ) : (L.X n).IsQuasicoherent :=
    inferInstanceAs
      (tilde ((Koszul.coefficientComplex (ModuleCat.of A (A ⧸ I)) s).X n)).IsQuasicoherent
  exact coordinateComplexIso A _ L

/-- The concrete quotient-Koszul comparison preserves the literal Koszul differential. -/
theorem quotientKoszulDifferential (A : CommRingCat.{u}) (I : Ideal A) (s : List A)
    (n m : ℕ) :
    let L := ((tilde.functor A).mapHomologicalComplex _).obj
      (Koszul.coefficientComplex (ModuleCat.of A (A ⧸ I)) s)
    (((tilde.functor A).mapHomologicalComplex _).obj
      (coordinateComplex A _ L)).d n m ≫ (quotientKoszulCoordinates A I s).hom.f m =
        (quotientKoszulCoordinates A I s).hom.f n ≫ L.d n m :=
  ((quotientKoszulCoordinates A I s).hom.comm n m).symm

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated h]
  {U : (F.leftIntermediateImageProduct G H).Opens} (hU : IsAffineOpen U)
  (K : ChainComplex (F.leftIntermediateSupportProduct G H).Modules ℕ)
  [∀ n, (K.X n).IsQuasicoherent]
  (q : Spec Γ(F.leftIntermediateSupportProduct G H,
    (F.leftIntermediateImageMap G H) ⁻¹ᵁ U))

/-- The true finite image-product chart constructs coordinates of a genuinely
given QC complex and recovers each original source stalk with its actual action. -/
def actualIntermediateSupportCoordinates :
    ((tilde.functor Γ(F.leftIntermediateSupportProduct G H,
        (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) ⋙ functor q).mapHomologicalComplex _).obj
        (wholeChartCoordinateComplex _ (F.leftIntermediateImageMap G H) hU K) ≅
      (Functor.mapHomologicalComplex
        (functor (sourceChart (F.leftIntermediateImageMap G H) hU q) ⋙
        ModuleCat.restrictScalars
          (inv ((sourceChart (F.leftIntermediateImageMap G H) hU).stalkMap q)).hom)
          _).obj K :=
  wholeChartStalkIso _ _ hU K q

/-- The actual intermediate-support comparison keeps every original differential. -/
theorem actualIntermediateSupportDifferential (n m : ℕ) :
    (((tilde.functor Γ(F.leftIntermediateSupportProduct G H,
        (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) ⋙ functor q).mapHomologicalComplex _).obj
        (wholeChartCoordinateComplex _ (F.leftIntermediateImageMap G H) hU K)).d n m ≫
        (actualIntermediateSupportCoordinates F G H hU K q).hom.f m =
      (actualIntermediateSupportCoordinates F G H hU K q).hom.f n ≫
        ((Functor.mapHomologicalComplex
        (functor (sourceChart (F.leftIntermediateImageMap G H) hU q) ⋙
          ModuleCat.restrictScalars
            (inv ((sourceChart (F.leftIntermediateImageMap G H) hU).stalkMap q)).hom)
            _).obj K).d n m :=
  ((actualIntermediateSupportCoordinates F G H hU K q).hom.comm n m).symm

end Motivic.MotivicTest.AffineQuasicoherentComplex
