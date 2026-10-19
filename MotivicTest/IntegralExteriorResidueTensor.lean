/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.ResidueTensor
public import MotivicTest.IntegralGenericCoordinateFiber

/-!
# The original pair exterior algebra over its original residue extension

For arbitrary fields and actual SmoothSite correspondence generators, use the
accepted original pairMap, pairExteriorMap and Cartesian square. Flatness of
the actual exterior projection supplies its generic-point projection theorem.
The whole finite algebra over the target support-product generic stalk is
identified with the tensor of the two original ambient residue fields.

The source and target support products keep their actual closed immersions
into the whole intermediate products. This does not identify either support
product with its ambient product or declare its generic points ambient generic.
No comparison hypothesis, purity, separability, reducedness or branch choice
is supplied. All-branch indexing and degree/length regrouping are downstream.

Initially prepared source-only. The Cartesian prerequisite has since been
independently accepted. This packet's compiler and acceptance status is recorded
separately; source presence alone certifies neither.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Cycles
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.PrimeSpectrum
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open scoped TensorProduct
open MotivicTest.IntegralGenericFiniteImage

universe u

namespace MotivicTest.IntegralExteriorResidueTensor

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

local instance : IsFinite (F.incidenceMap G).toImage := F.incidenceToImage_isFinite G

/-- The projection is the original image-support exterior projection. -/
abbrev targetProjection := pullback.fst
  ((imageSupport F G z).val.subschemeι ≫ imageStructure F G) (H.projection ≫ Z.hom)

/-- Over an arbitrary field the actual exterior factor is flat. -/
theorem exteriorFactor_flat : Flat (H.projection ≫ Z.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (H.projection ≫ Z.hom)

/-- Flatness belongs to the literal target projection by actual base change. -/
theorem targetProjection_flat : Flat (targetProjection F G H z) := by
  let : Flat (H.projection ≫ Z.hom) := exteriorFactor_flat (H := H)
  change Flat (pullback.fst
    ((imageSupport F G z).val.subschemeι ≫ imageStructure F G) (H.projection ≫ Z.hom))
  infer_instance

/-- The generic target projects to the actual original integral generic point;
this is derived from flatness, rather than assumed as comparison data. -/
theorem targetProjection_generic (v : genericPoints (imageExterior F G H z)) :
    targetProjection F G H z v.1 = genericPoint (imageSupport F G z).val.subscheme :=
  MotivicTest.IntegralGenericCoordinateFiber.exteriorTargetGeneric_projection F G H z v

variable {U : (imageSupport F G z).val.subscheme.Opens} [Nonempty U] (hU : IsAffineOpen U)
  {V : (imageExterior F G H z).Opens} (hV : IsAffineOpen V)
  (hVU : V ≤ (targetProjection F G H z) ⁻¹ᵁ U)
  (v : genericPoints (imageExterior F G H z)) (hv : v.1 ∈ V)

/-- The original target residue field acts on the whole exterior target stalk
through the actual projection and accepted original coordinate/residue maps. -/
abbrev exteriorResidueAlgebra :
    Algebra ((F.incidenceMap G).image.residueField ((F.incidenceMap G).toImage z.1))
      ((imageExterior F G H z).presheaf.stalk v.1) :=
  (BaseChange.ResidueTensor.originalResidueToStalk
    (F.incidenceMap G).toImage z.1 hU (targetProjection F G H z) v.1
      (targetProjection_generic F G H z v)).toAlgebra

local notation "C" => FiniteCartesianAffineAlgebra.baseChangedTargetRing
  (Y' := imageExterior F G H z) (V := V)
local notation "D" => FiniteCartesianAffineAlgebra.baseChangedSourceRing
  (f' := pairExteriorMap F G H z) (V := V)
local notation "R" => (TopCat.Presheaf.stalk
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace
      (Scheme.toLocallyRingedSpace (imageExterior F G H z))))) (Subtype.val v) : CommRingCat)
local notation "L" => Scheme.residueField (Scheme.Hom.image (F.incidenceMap G))
  (Scheme.Hom.toImage (F.incidenceMap G) (Subtype.val z))
local notation "M" => Scheme.residueField (F.incidence G) (Subtype.val z)
local notation "B" => FiniteCartesianAffineAlgebra.sourceRing
  (f := pairMap F G z) (U := U)

/-- The actual entire finite exterior algebra is the tensor of the original
residue extension with the unreduced original exterior target stalk. -/
def actualExteriorResidueTensorEquiv :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra
      (f' := pairExteriorMap F G H z) (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra (⟨v.1, hv⟩ : V)
    let := exteriorResidueAlgebra F G H z hU v
    let := ((F.incidenceMap G).toImage.residueFieldMap z.1).hom.toAlgebra
    R ⊗[C] D ≃ₐ[R] R ⊗[L] M :=
  BaseChange.ResidueTensor.wholeStalkResidueEquiv
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v)

/-- The whole-algebra comparison preserves the whole R-action, including every
nilpotent in the exterior target generic stalk. -/
theorem actualExteriorResidueTensor_scalarSquare :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra
      (f' := pairExteriorMap F G H z) (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra (⟨v.1, hv⟩ : V)
    let := exteriorResidueAlgebra F G H z hU v
    let := ((F.incidenceMap G).toImage.residueFieldMap z.1).hom.toAlgebra
    (actualExteriorResidueTensorEquiv F G H z hU hV hVU v hv).toRingHom.comp
        (algebraMap R (R ⊗[C] D)) = algebraMap R (R ⊗[L] M) :=
  BaseChange.ResidueTensor.wholeStalkResidueEquiv_scalarSquare
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v)

/-- The numerator square contains the actual source exterior projection on
sections and the accepted original source chart/residue map. -/
theorem actualExteriorResidueTensor_source (r : R) (b : B) :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra
      (f' := pairExteriorMap F G H z) (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra (⟨v.1, hv⟩ : V)
    let := exteriorResidueAlgebra F G H z hU v
    let := ((F.incidenceMap G).toImage.residueFieldMap z.1).hom.toAlgebra
    actualExteriorResidueTensorEquiv F G H z hU hV hVU v hv
        (r ⊗ₜ[C] FiniteCartesianAffineAlgebra.sourceSectionMap
          (pairExteriorMap_isPullback F G H z) hVU b) =
      r ⊗ₜ[L] BaseChange.ResidueTensor.originalSourceNumerator
        (F.incidenceMap G).toImage z.1 hU b :=
  BaseChange.ResidueTensor.wholeStalkResidueEquiv_source
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v) r b

/-- The original source-numerator map commutes as an equality of ring maps
into the entire exterior algebra and the original residue tensor. -/
theorem actualExteriorResidueTensor_numeratorSquare :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra
      (f' := pairExteriorMap F G H z) (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra (⟨v.1, hv⟩ : V)
    let := exteriorResidueAlgebra F G H z hU v
    let := ((F.incidenceMap G).toImage.residueFieldMap z.1).hom.toAlgebra
    (actualExteriorResidueTensorEquiv F G H z hU hV hVU v hv).toRingHom.comp
        ((Algebra.TensorProduct.includeRight.toRingHom : D →+* R ⊗[C] D).comp
          (FiniteCartesianAffineAlgebra.sourceSectionMap
            (pairExteriorMap_isPullback F G H z) hVU).hom) =
      (Algebra.TensorProduct.includeRight.toRingHom : M →+* R ⊗[L] M).comp
        (BaseChange.ResidueTensor.originalSourceNumerator
          (F.incidenceMap G).toImage z.1 hU).hom :=
  BaseChange.ResidueTensor.wholeStalkResidueEquiv_numeratorSquare
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v)

include hV in
/-- Finiteness holds for the entire actual stalk algebra, not one residue field
or a selected maximal localization. -/
theorem actualExteriorWhole_finite :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra
      (f' := pairExteriorMap F G H z) (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra (⟨v.1, hv⟩ : V)
    Module.Finite R (R ⊗[C] D) :=
  FiniteCartesianAffineAlgebra.wholeStalk_finite
    (pairExteriorMap_isPullback F G H z) hV ⟨v.1, hv⟩

/-- Both support exteriors retain their original ambient inclusions and the
literal original whole intermediate-image map in the same square. -/
@[reassoc] theorem actualExteriorAmbientSquare :
    pairExteriorMap F G H z ≫ imageExteriorInclusion F G H z =
      pairExteriorInclusion F G H z ≫ F.leftIntermediateImageMap G H :=
  pairExteriorMap_ambient F G H z

/-- This whole stalk algebra also has the literal target-localization model
used by the all-maximal-points API. No indexing theorem is presumed here. -/
def actualExteriorStalkToLocalEquiv :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra
      (f' := pairExteriorMap F G H z) (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra (⟨v.1, hv⟩ : V)
    R ⊗[C] D ≃ₐ[C] FiniteFiber.localAlgebra C D (hV.primeIdealOf ⟨v.1, hv⟩) :=
  FiniteCartesianAffineAlgebra.wholeStalkToLocalEquiv
    (f' := pairExteriorMap F G H z) hV ⟨v.1, hv⟩

end MotivicTest.IntegralExteriorResidueTensor
