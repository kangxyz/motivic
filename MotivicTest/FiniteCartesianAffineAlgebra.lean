/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.CartesianAffineAlgebra
public import MotivicTest.IntegralGenericFiniteImage

/-!
# Actual pair-support exterior finite algebras

This consumer starts from the independently constructed original pair-to-image
finite map, its two integral point closures, and their actual exterior map.
It uses the proved Cartesian square from `MotivicTest.IntegralGenericFiniteImage`,
not a supplied tensor isomorphism or a bijection of source points.

The full affine inverse-image algebra and its localization at the actual
exterior target stalk are compared with the original-coordinate tensor.
The exterior source and target schemes, and the target stalk, are not reduced.
The final conversion from original coordinate localization to the original
ambient residue-field action is a separate attachment obligation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite isArtinianRing_stalk_of_mem_genericPoints)
open _root_.AlgebraicGeometry.Scheme.Hom.FiniteCartesianAffineAlgebra (baseChangedAlgebra
  baseChangedSourceRing baseChangedTargetRing coordinateAlgEquiv coordinateAlgEquiv_source
  coordinateAlgEquiv_target coordinate_isPushout originalGerm_stalkSquare sourceAlgebra
  sourceRing sourceSectionMap targetAlgebra targetStalkAlgebra wholeStalkEquiv
  wholeStalkEquiv_scalarSquare wholeStalkEquiv_source wholeStalkToLocalEquiv wholeStalk_finite)
open _root_.PrimeSpectrum.FiniteFiber (localAlgebra)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open scoped TensorProduct
open MotivicTest.IntegralGenericFiniteImage

universe u

namespace MotivicTest.FiniteCartesianAffineAlgebra

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

local notation "f₀" => pairMap F G z
local notation "f₁" => pairExteriorMap F G H z
/-- The actual exterior target projection to the original integral image support. -/
abbrev targetProjection := pullback.fst
  ((imageSupport F G z).val.subschemeι ≫ imageStructure F G) (H.projection ≫ Z.hom)

local notation "g₀" => targetProjection F G H z
local notation "sq" => pairExteriorMap_isPullback F G H z

variable {U : (imageSupport F G z).val.subscheme.Opens} (hU : IsAffineOpen U)
  {V : (imageExterior F G H z).Opens} (hV : IsAffineOpen V)
  (hVU : V ≤ (targetProjection F G H z) ⁻¹ᵁ U)

/-- The original integral-image affine target coordinate ring. -/
abbrev originalTargetRing : CommRingCat.{u} := Γ((imageSupport F G z).val.subscheme, U)

local notation "A" => originalTargetRing F G z (U := U)
local notation "B" => sourceRing (f := f₀) (U := U)
local notation "C" => baseChangedTargetRing
  (Y' := imageExterior F G H z) (V := V)
local notation "D" => baseChangedSourceRing (f' := f₁) (V := V)

include hU hV in
/-- The actual exterior pair-support square yields the literal section-ring pushout. -/
theorem actualExteriorCoordinatePushout :
    IsPushout ((g₀).appLE U V hVU) ((f₀).app U) ((f₁).app V)
      (sourceSectionMap sq hVU) :=
  coordinate_isPushout sq hU hV hVU

/-- The entire exterior inverse-image ring is the actual original-coordinate tensor algebra. -/
def actualExteriorCoordinateAlgEquiv :
    let := sourceAlgebra (f := f₀) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f₁) (V := V)
    D ≃ₐ[C] C ⊗[A] B :=
  coordinateAlgEquiv sq hU hV hVU

/-- The source map is the original exterior projection on actual sections. -/
theorem actualExteriorCoordinate_source (b : B) :
    let := sourceAlgebra (f := f₀) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f₁) (V := V)
    actualExteriorCoordinateAlgEquiv F G H z hU hV hVU
        (sourceSectionMap sq hVU b) = 1 ⊗ₜ[A] b :=
  coordinateAlgEquiv_source sq hU hV hVU b

/-- The scalar map is the actual finite exterior support-map action on sections. -/
theorem actualExteriorCoordinate_target (c : C) :
    let := sourceAlgebra (f := f₀) (U := U)
    let := targetAlgebra hVU
    let := baseChangedAlgebra (f' := f₁) (V := V)
    actualExteriorCoordinateAlgEquiv F G H z hU hV hVU ((f₁).app V c) = c ⊗ₜ[A] (1 : B) :=
  coordinateAlgEquiv_target sq hU hV hVU c

variable (y : V)

/-- The literal unreduced exterior target structure stalk. -/
abbrev exteriorTargetStalk : CommRingCat.{u} := (imageExterior F G H z).presheaf.stalk y.1

local notation "R" => exteriorTargetStalk F G H z y

/-- The target is the original exterior structure stalk, including its nilpotents;
the source algebra is the whole finite algebra, including every maximal branch. -/
def actualExteriorWholeStalkEquiv :
    let := sourceAlgebra (f := f₀) (U := U)
    let := baseChangedAlgebra (f' := f₁) (V := V)
    let := targetStalkAlgebra y
    let := (((imageExterior F G H z).presheaf.germ V y.1 y.2).hom.comp
      ((g₀).appLE U V hVU).hom).toAlgebra
    R ⊗[C] D ≃ₐ[R] R ⊗[A] B :=
  wholeStalkEquiv sq hU hV hVU y

/-- The whole-stalk equivalence retains the literal original source numerator map. -/
theorem actualExteriorWholeStalk_source (r : R) (b : B) :
    let := sourceAlgebra (f := f₀) (U := U)
    let := baseChangedAlgebra (f' := f₁) (V := V)
    let := targetStalkAlgebra y
    let := (((imageExterior F G H z).presheaf.germ V y.1 y.2).hom.comp
      ((g₀).appLE U V hVU).hom).toAlgebra
    actualExteriorWholeStalkEquiv F G H z hU hV hVU y
        (r ⊗ₜ[C] sourceSectionMap sq hVU b) =
      r ⊗ₜ[A] b :=
  wholeStalkEquiv_source sq hU hV hVU y r b

/-- The comparison is an algebra equivalence over the unreduced original exterior stalk. -/
theorem actualExteriorWholeStalk_scalarSquare :
    let := sourceAlgebra (f := f₀) (U := U)
    let := baseChangedAlgebra (f' := f₁) (V := V)
    let := targetStalkAlgebra y
    let := (((imageExterior F G H z).presheaf.germ V y.1 y.2).hom.comp
      ((g₀).appLE U V hVU).hom).toAlgebra
    (actualExteriorWholeStalkEquiv F G H z hU hV hVU y).toRingHom.comp
        (algebraMap R (R ⊗[C] D)) = algebraMap R (R ⊗[A] B) :=
  wholeStalkEquiv_scalarSquare sq hU hV hVU y

/-- This is the same all-branch finite algebra used by the existing maximal-fiber API. -/
def actualExteriorStalkToLocalEquiv :
    let := baseChangedAlgebra (f' := f₁) (V := V)
    let := targetStalkAlgebra y
    R ⊗[C] D ≃ₐ[C] localAlgebra C D (hV.primeIdealOf y) :=
  wholeStalkToLocalEquiv (f' := f₁) hV y

/-- The original-coordinate action factors through the actual exterior projection stalk map. -/
@[reassoc] theorem actualExteriorGermStalkSquare :
    (g₀).appLE U V hVU ≫ (imageExterior F G H z).presheaf.germ V y.1 y.2 =
      (imageSupport F G z).val.subscheme.presheaf.germ U (g₀ y.1) (hVU y.2) ≫
        (g₀).stalkMap y.1 :=
  originalGerm_stalkSquare hVU y

include hV in
/-- Finiteness is a property of the entire actual exterior algebra over its target stalk. -/
theorem actualExteriorWhole_finite :
    let := baseChangedAlgebra (f' := f₁) (V := V)
    let := targetStalkAlgebra y
    Module.Finite R (R ⊗[C] D) :=
  wholeStalk_finite sq hV y

/-- At an actual generic exterior target the stalk is Artinian under the actual
Noetherian hypothesis. Neither this theorem nor the algebra comparison makes it a field. -/
theorem actualExteriorGenericStalk_artinian
    [IsLocallyNoetherian (imageExterior F G H z)]
    (w : genericPoints (imageExterior F G H z)) :
    IsArtinianRing ((imageExterior F G H z).presheaf.stalk w.1) :=
  isArtinianRing_stalk_of_mem_genericPoints w.1 w.2

end MotivicTest.FiniteCartesianAffineAlgebra
