/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorDegreeLength
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian
public import MotivicTest.IntegralExteriorResidueTensor

/-!
# Actual pair-exterior degree-length consumers over arbitrary fields

The complete actual generic fiber of the original pairExteriorMap is weighted
by its whole support-stalk lengths and its individual scheme residue degrees.
Its total is the original pair-incidence degree times the entire target support
multiplicity. The base field is arbitrary, with no separability or geometric
reducedness hypothesis. The actual target's Noetherian property and generic
projection are derived from the original SmoothSite geometry.

A second consumer retains the actual exterior closed-fiber rings and the actual
whole intermediate-image map's residue degrees. The original support immersion
comparisons identify their lengths, without identifying support points with
ambient generic points. The signed pair Tor coefficient can multiply the full
balance without choosing or merging source branches.

SOURCE-ONLY: no compilation or prerequisite acceptance is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open MotivicTest.IntegralGenericFiniteImage MotivicTest.IntegralExteriorResidueTensor
open Motivic.IntegralExteriorDegreeLength

universe u

namespace MotivicTest.IntegralExteriorDegreeLength

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

local instance degreeLength_consumerPairToImageFinite : IsFinite (F.incidenceMap G).toImage :=
  F.incidenceToImage_isFinite G

/-- Local Noetherianity belongs to the actual image-support exterior. It follows
from the smooth ambient product, the actual support immersion, and base change. -/
local instance degreeLength_consumerImageExteriorNoetherian :
    IsLocallyNoetherian (imageExterior F G H z) := by
  let degreeLength_consumerSourceNoetherian : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
  let degreeLength_consumerProductNoetherian : IsLocallyNoetherian (pullback X.hom Z.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X.left) (pullback.fst X.hom Z.hom)
  let degreeLength_consumerImageNoetherian : IsLocallyNoetherian (F.incidenceMap G).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback X.hom Z.hom)
      (F.incidenceMap G).imageι
  let degreeLength_consumerImageSupportNoetherian :
      IsLocallyNoetherian (imageSupport F G z).val.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := (F.incidenceMap G).image)
      (imageSupport F G z).val.subschemeι
  exact LocallyOfFiniteType.isLocallyNoetherian
    (Y := (imageSupport F G z).val.subscheme) (targetProjection F G H z)

/-- Passing through the actual whole image retains the original incidence degree. -/
theorem actualPairToImage_residueDegree :
    (F.incidenceMap G).toImage.residueDegree z.1 = (F.incidenceMap G).residueDegree z.1 := by
  have he := congrArg (fun m => m.residueDegree z.1) (F.incidenceMap G).toImage_imageι
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul] using he

/-- The actual pair exterior satisfies the full degree-length formula, with
no affine-chart data, branch selection, or degree-balance hypothesis supplied. -/
theorem actualPairExterior_degreeLength (v : genericPoints (imageExterior F G H z)) :
    actualGenericFiberDegreeLengthSum (pairExteriorMap F G H z) v.1 =
      ((F.incidenceMap G).residueDegree z.1 : ℤ) * (genericMultiplicity v : ℤ) := by
  have h := actualGenericFiberDegreeLengthSum_eq (F.incidenceMap G).toImage z.1
    (pairExteriorMap_isPullback F G H z) v (targetProjection_generic F G H z v)
  rwa [actualPairToImage_residueDegree F G z] at h

/-- The same statement explicitly displays ALL actual generic source branches
above v, with each individual actual residue degree. Collisions are summed. -/
theorem actualPairExterior_allBranches (v : genericPoints (imageExterior F G H z)) :
    letI :=
      actualGenericFiberFintype (pairExteriorMap F G H z) v.1
    (∑ w : {w : genericPoints (pairExterior F G H z) // pairExteriorMap F G H z w.1 = v.1},
      (genericMultiplicity w.1 : ℤ) * ((pairExteriorMap F G H z).residueDegree w.1.1 : ℤ)) =
        ((F.incidenceMap G).residueDegree z.1 : ℤ) * (genericMultiplicity v : ℤ) :=
  actualPairExterior_degreeLength F G H z v

/-- In actual ambient closed-fiber notation, the full-source quotient length
and the original intermediate-image map's residue degree give the same balance. -/
theorem actualPairExterior_closedFiberLengthBalance
    (v : genericPoints (imageExterior F G H z)) :
    letI :=
      actualGenericFiberFintype (pairExteriorMap F G H z) v.1
    (∑ w : {w : genericPoints (pairExterior F G H z) // pairExteriorMap F G H z w.1 = v.1},
      ((Module.length
        (F.leftExteriorClosedFiber G H (pairExteriorInclusion F G H z w.1.1))
        (F.leftExteriorClosedFiber G H (pairExteriorInclusion F G H z w.1.1))).toNat : ℤ) *
          ((F.leftIntermediateImageMap G H).residueDegree
            (pairExteriorInclusion F G H z w.1.1) : ℤ)) =
      ((F.incidenceMap G).residueDegree z.1 : ℤ) *
        ((Module.length
          (Koszul.coefficientClosedFiber
            ((pullback.fst (imageStructure F G) (H.projection ≫ Z.hom)).stalkMap
              (imageExteriorInclusion F G H z v.1)).hom)
          (Koszul.coefficientClosedFiber
            ((pullback.fst (imageStructure F G) (H.projection ≫ Z.hom)).stalkMap
              (imageExteriorInclusion F G H z v.1)).hom)).toNat : ℤ) := by
  classical
  let degreeLength_consumerFiberFintype := actualGenericFiberFintype (pairExteriorMap F G H z) v.1
  have hs (w : genericPoints (pairExterior F G H z)) :
      (Module.length
        (F.leftExteriorClosedFiber G H (pairExteriorInclusion F G H z w.1))
        (F.leftExteriorClosedFiber G H (pairExteriorInclusion F G H z w.1))).toNat =
      genericMultiplicity w :=
    congrArg ENat.toNat (ringLength_eq_of_ringEquiv (pairExteriorClosedFiberEquiv F G H z w))
  have ht := congrArg ENat.toNat
    (ringLength_eq_of_ringEquiv (imageExteriorClosedFiberEquiv F G H z v))
  change _ = ((F.incidenceMap G).residueDegree z.1 : ℤ) *
    ((Module.length _ _).toNat : ℤ)
  rw [ht]
  change _ = ((F.incidenceMap G).residueDegree z.1 : ℤ) * (genericMultiplicity v : ℤ)
  rw [← actualPairExterior_allBranches F G H z v]
  apply Finset.sum_congr rfl
  intro w _
  rw [hs, ← pairExteriorMap_residueDegree F G H z w.1.1]

/-- The original signed pair Tor coefficient weights every actual exterior
branch together. No constancy of the individual exterior residue degrees enters. -/
theorem actualPairTorExterior_degreeLength (v : genericPoints (imageExterior F G H z)) :
    F.incidenceTorCoefficient (S := Spec (.of k)) G z *
        actualGenericFiberDegreeLengthSum (pairExteriorMap F G H z) v.1 =
      (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
        ((F.incidenceMap G).residueDegree z.1 : ℤ)) * (genericMultiplicity v : ℤ) := by
  rw [actualPairExterior_degreeLength F G H z v, mul_assoc]

end MotivicTest.IntegralExteriorDegreeLength
